/* CLI host operations. Inference: parent Wasm + compiled WGSL. Tokenization
 * and sampling: existing Lean-generated Wasm. Float conversion: Wasm only. */
static void packed_invoke(Runtime *runtime,const char *name,const uint64_t *args,size_t argc,uint64_t *out,size_t resultc) {
  wasmtime_func_t function=get_func(runtime,name);wasmtime_val_t a[6]={0},r[4]={0};
  packed_need(argc<=6&&resultc<=4,"packed CLI call arity");
  for(size_t i=0;i<argc;i++){a[i].kind=WASMTIME_I64;a[i].of.i64=(int64_t)args[i];}
  wasm_trap_t *trap=NULL;wasmtime_error_t *error=wasmtime_func_call(runtime->context,&function,a,argc,r,resultc,&trap);
  if(error){print_error(error);exit(1);}if(trap){print_trap(trap);exit(1);}
  for(size_t i=0;i<resultc;i++){packed_need(r[i].kind==WASMTIME_I64,"packed CLI result type");out[i]=(uint64_t)r[i].of.i64;}
}
static void packed_path(char *path,size_t capacity,const char *directory,const char *name) {
  packed_need(snprintf(path,capacity,"%s/%s",directory,name)<(int)capacity,"packed CLI path");
}
static U64List packed_result(Runtime *runtime,uint64_t pointer,size_t maximum) {
  uint64_t count=read_u64_at(runtime,pointer);packed_need(count<=maximum,"Wasm array result size");
  U64List result={calloc(count?count:1,8),(size_t)count};packed_need(result.items!=NULL,"Wasm result allocation");
  memcpy(result.items,packed_region(runtime,pointer+8,count*8),count*8);return result;
}
static U64List packed_tokens(Runtime *runtime,U64List table,uint64_t op,U64List input) {
  reset_runtime(runtime);uint64_t args[3]={op,alloc_u64_array(runtime,table),alloc_u64_array(runtime,input)},pointer;
  packed_invoke(runtime,"tokens",args,3,&pointer,1);return packed_result(runtime,pointer,65536);
}
static uint8_t *packed_forward_cli(Runtime *runtime,uint64_t weights,uint64_t *cache,uint64_t *cache_size,uint64_t token,size_t position) {
  uint64_t args[]={weights,497759232,*cache,*cache_size,token,position},out[4];
  packed_invoke(runtime,"cachedStep",args,6,out,4);
  packed_need(out[1]==(position+1)*73728&&out[3]==201028,"packed step output lengths");
  uint8_t *logits=malloc(201028);packed_need(logits!=NULL,"logit allocation");
  memcpy(logits,packed_region(runtime,out[2],201028),201028);
  if(*cache)packed_invoke(runtime,"release",cache,1,NULL,0);
  packed_invoke(runtime,"release",&out[2],1,NULL,0);*cache=out[0];*cache_size=out[1];return logits;
}
static uint64_t packed_sample(Runtime *sampler,Runtime *transfer,const uint8_t *logits,uint64_t settings[3]) {
  memcpy(packed_region(transfer,161000000,201028),logits,201028);
  uint64_t convert[]={1,50257};packed_invoke(transfer,"convert",convert,2,NULL,0);
  reset_runtime(sampler);
  U64List words={(uint64_t *)packed_region(transfer,160000000,50257*8),50257},parameters={settings,3};
  uint64_t args[]={5,alloc_u64_array(sampler,words),alloc_u64_array(sampler,(U64List){NULL,0}),
    alloc_u64_array(sampler,parameters),0},pointer;
  packed_invoke(sampler,"compute",args,5,&pointer,1);U64List result=packed_result(sampler,pointer,2);
  packed_need(result.len==2&&result.items[0]<50257,"Wasm sampled result");
  uint64_t token=result.items[0];settings[2]=result.items[1];free(result.items);return token;
}
static void command_packed_run(Runtime *model,int argc,char **argv) {
  packed_need(argc>=3,"usage: packed-run BUNDLE --prompt TEXT [--generate 16] [--temperature 0|0.7|0.8|1] [--seed 42] [--trace FILE]");
  const char *prompt=NULL,*trace_path=NULL;size_t count=16;uint64_t settings[3]={0,40,42};
  for(int i=1;i<argc;i++) {
    packed_need(i+1<argc,"missing packed CLI option value");const char *option=argv[i],*value=argv[++i];
    if(!strcmp(option,"--prompt")){packed_need(prompt==NULL,"duplicate prompt");prompt=value;}
    else if(!strcmp(option,"--generate")){count=parse_u64(value);packed_need(count>0&&count<128,"generation length");}
    else if(!strcmp(option,"--seed")){settings[2]=parse_u64(value);packed_need(settings[2]>0,"seed must be positive");}
    else if(!strcmp(option,"--trace")){packed_need(trace_path==NULL,"duplicate trace");trace_path=value;}
    else if(!strcmp(option,"--temperature")) {
      if(!strcmp(value,"0"))settings[0]=0;
      else if(!strcmp(value,"0.7"))settings[0]=0x3fe6666666666666;
      else if(!strcmp(value,"0.8"))settings[0]=0x3fe999999999999a;
      else if(!strcmp(value,"1"))settings[0]=0x3ff0000000000000;
      else die("temperature must be 0, 0.7, 0.8 or 1");
    } else die("unknown packed CLI option");
  }
  packed_need(prompt&&strlen(prompt)>0&&strlen(prompt)<=16384,"prompt must contain 1..16384 UTF-8 bytes");
  char file[4096];Runtime tokenizer,sampler,transfer;
  packed_path(file,sizeof file,argv[0],"model.wasm");init_runtime(model,file);
  packed_path(file,sizeof file,argv[0],"tokenizer.wasm");init_runtime(&tokenizer,file);
  packed_path(file,sizeof file,argv[0],"sampler.wasm");init_runtime(&sampler,file);
  packed_path(file,sizeof file,argv[0],"transfer.wasm");init_runtime(&transfer,file);
  size_t table_size;packed_path(file,sizeof file,argv[0],"tokenizer.bin");uint8_t *table_bytes=read_file(file,&table_size);
  packed_need(table_size%8==0,"tokenizer table size");U64List table={(uint64_t *)table_bytes,table_size/8};
  U64List text={calloc(strlen(prompt),8),strlen(prompt)};packed_need(text.items!=NULL,"prompt allocation");
  for(size_t i=0;i<text.len;i++)text.items[i]=(unsigned char)prompt[i];
  U64List tokens=packed_tokens(&tokenizer,table,0,text);free(text.items);
  packed_need(tokens.len>0&&tokens.len+count<=128,"prompt and requested completion exceed 128 tokens");
  for(size_t i=0;i<tokens.len;i++)packed_need(tokens.items[i]<50257,"tokenizer rejected input");
  size_t weight_size;packed_path(file,sizeof file,argv[0],"weights.bin");uint8_t *weight_bytes=read_file(file,&weight_size);
  packed_need(weight_size==497759232,"packed checkpoint size");uint64_t weights=alloc_bytes(model,weight_bytes,weight_size);free(weight_bytes);
  fprintf(stderr,"Packed FP32 GPT-2: Wasm controller and sampler; WebGPU matrix calls.\n");
  uint64_t cache=0,cache_size=0;uint8_t *logits=NULL;
  for(size_t i=0;i<tokens.len;i++){free(logits);logits=packed_forward_cli(model,weights,&cache,&cache_size,tokens.items[i],i);}
  FILE *trace=NULL;if(trace_path){trace=fopen(trace_path,"wbx");packed_need(trace!=NULL,"trace file must be new and writable");}
  fwrite(prompt,1,strlen(prompt),stdout);fflush(stdout);
  for(size_t i=0;i<count;i++) {
    uint64_t token=packed_sample(&sampler,&transfer,logits,settings);
    if(trace)packed_need(fwrite(&token,8,1,trace)==1&&fwrite(logits,1,201028,trace)==201028,"trace write");
    free(logits);logits=NULL;if(token==50256)break;
    U64List decoded=packed_tokens(&tokenizer,table,1,(U64List){&token,1});
    for(size_t j=0;j<decoded.len;j++){packed_need(decoded.items[j]<256,"decoded byte");fputc((int)decoded.items[j],stdout);}
    free(decoded.items);fflush(stdout);
    if(i+1<count)logits=packed_forward_cli(model,weights,&cache,&cache_size,token,tokens.len+i);
  }
  putchar('\n');if(trace)fclose(trace);free(logits);free(tokens.items);free(table_bytes);
  if(cache)packed_invoke(model,"release",&cache,1,NULL,0);packed_invoke(model,"release",&weights,1,NULL,0);
  wasmtime_store_delete(tokenizer.store);wasm_engine_delete(tokenizer.engine);
  wasmtime_store_delete(sampler.store);wasm_engine_delete(sampler.engine);
  wasmtime_store_delete(transfer.store);wasm_engine_delete(transfer.engine);
}

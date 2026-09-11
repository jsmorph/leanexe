#include <wasm.h>
#include <wasmtime.h>
#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

_Static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, "little-endian files required");
static void require(int ok,const char *message) { if(!ok){fprintf(stderr,"%s: %s\n",message,strerror(errno));exit(1);} }
static void checked(wasmtime_error_t *error,wasm_trap_t *trap) {
 if(error){wasm_name_t m;wasmtime_error_message(error,&m);fprintf(stderr,"%.*s\n",(int)m.size,m.data);wasm_byte_vec_delete(&m);wasmtime_error_delete(error);exit(1);}
 if(trap){wasm_message_t m;wasm_trap_message(trap,&m);fprintf(stderr,"%.*s\n",(int)m.size,m.data);wasm_byte_vec_delete(&m);wasm_trap_delete(trap);exit(1);}
}
static char *name(const char *directory,const char *stem,int index,const char *suffix) {
 size_t length=strlen(directory)+strlen(stem)+strlen(suffix)+40;char *p=malloc(length);require(p!=NULL,"path allocation");
 snprintf(p,length,"%s/%s%02d%s",directory,stem,index,suffix);return p;
}
static uint8_t *read_all(const char *path,size_t *length) {
 FILE *f=fopen(path,"rb");require(f!=NULL,path);require(fseek(f,0,SEEK_END)==0,"seek");long size=ftell(f);require(size>=0,"file length");rewind(f);
 uint8_t *data=malloc((size_t)size+1);require(data!=NULL,"file allocation");require(fread(data,1,(size_t)size,f)==(size_t)size,"read");require(fclose(f)==0,"close");*length=(size_t)size;return data;
}
static void write_new(const char *path,const void *data,size_t length) {
 FILE *f=fopen(path,"wbx");require(f!=NULL,path);require(fwrite(data,1,length,f)==length,"write");require(fclose(f)==0,"close");
}
static wasmtime_extern_t exported(wasmtime_context_t *context,wasmtime_instance_t *instance,const char *symbol,wasmtime_extern_kind_t kind) {
 wasmtime_extern_t out;require(wasmtime_instance_export_get(context,instance,symbol,strlen(symbol),&out),symbol);require(out.kind==kind,"export type");return out;
}
static void prepare(wasm_engine_t *engine,char **argv) {
 for(int i=0;i<4;i++){
  size_t length;uint8_t *data=read_all(argv[3+i],&length);wasm_byte_vec_t wasm={0};
  if(i==3){checked(wasmtime_wat2wasm((const char *)data,length,&wasm),NULL);free(data);data=(uint8_t *)wasm.data;length=wasm.size;}
  wasmtime_module_t *module=NULL;checked(wasmtime_module_new(engine,data,length,&module),NULL);
  if(i==3){char *p=name(argv[2],"module-",i,".wasm");write_new(p,data,length);free(p);wasm_byte_vec_delete(&wasm);}else free(data);
  wasm_byte_vec_t compiled;checked(wasmtime_module_serialize(module,&compiled),NULL);
  char *p=name(argv[2],"module-",i,".cwasm");write_new(p,compiled.data,compiled.size);free(p);wasm_byte_vec_delete(&compiled);wasmtime_module_delete(module);
 }
}
static size_t block_rows(size_t n,int block) { return n*(size_t)(block+1)/24-n*(size_t)block/24; }
static void read_block(const char *directory,size_t n,int block,size_t offset,void *out,size_t length) {
 char *p=name(directory,"block-",block,".bin");FILE *f=fopen(p,"rb");require(f!=NULL,p);free(p);
 require(fseek(f,0,SEEK_END)==0,"seek");long size=ftell(f);size_t cells=block_rows(n,block)*n;
 require(size>=0&&((size_t)size==cells*40||(size_t)size==cells*32),"block length");
 size_t stride=(size_t)size/cells;require(offset%40==0&&length%40==0&&offset+length<=cells*40,"block range");
 require(fseek(f,(long)(offset/40*stride),SEEK_SET)==0,"seek");
 if(stride==40)require(fread(out,1,length,f)==length,"block read");
 else{
  size_t packed_length=length/40*32;uint8_t *packed=malloc(packed_length);require(packed!=NULL,"packed allocation");
  require(fread(packed,1,packed_length,f)==packed_length,"block read");
  for(size_t i=0;i<length/40;i++){memcpy((uint8_t *)out+i*40,packed+i*32,32);memset((uint8_t *)out+i*40+32,0,8);}free(packed);
 }
 require(fclose(f)==0,"close");
}
int main(int argc,char **argv) {
 require(argc==7||argc==8,"usage: prepare cache side.wasm flux.wasm cell.wasm worker.wat | cache init|scan|x|y mesh block input output ratio");
 wasm_engine_t *engine=wasm_engine_new();require(engine!=NULL,"engine");
 if(strcmp(argv[1],"prepare")==0){require(argc==7,"prepare arguments");prepare(engine,argv);wasm_engine_delete(engine);return 0;}
 require(argc==8,"worker arguments");
 int mode=strcmp(argv[2],"scan")==0?0:strcmp(argv[2],"x")==0?1:strcmp(argv[2],"y")==0?2:strcmp(argv[2],"init")==0?3:-1;require(mode>=0,"worker mode");
 char *end;long mesh=strtol(argv[3],&end,10);require(*end==0&&mesh>=24&&mesh<=800&&mesh%2==0,"mesh");size_t n=(size_t)mesh;
 long id=strtol(argv[4],&end,10);require(*end==0&&id>=0&&id<24,"block index");int block=(int)id;
 uint64_t ratio=strtoull(argv[7],&end,16);require(*end==0,"ratio word");size_t rows=block_rows(n,block),start=n*(size_t)block/24;
 wasmtime_store_t *store=wasmtime_store_new(engine,NULL,NULL);require(store!=NULL,"store");wasmtime_context_t *context=wasmtime_store_context(store);
 wasmtime_instance_t instances[4];wasmtime_extern_t imports[3];const char *symbols[3]={"sideCheckedBits","fluxCheckedBits","cellCheckedBits"};
 for(int i=0;i<4;i++){
  char *p=name(argv[1],"module-",i,".cwasm");wasmtime_module_t *module=NULL;checked(wasmtime_module_deserialize_file(engine,p,&module),NULL);free(p);
  wasm_trap_t *trap=NULL;wasmtime_error_t *error=wasmtime_instance_new(context,module,i==3?imports:NULL,i==3?3:0,&instances[i],&trap);checked(error,trap);wasmtime_module_delete(module);
  if(i<3)imports[i]=exported(context,&instances[i],symbols[i],WASMTIME_EXTERN_FUNC);
 }
 wasmtime_memory_t memory=exported(context,&instances[3],"memory",WASMTIME_EXTERN_MEMORY).of.memory;
 uint8_t *data=wasmtime_memory_data(context,&memory);require(wasmtime_memory_data_size(context,&memory)>=4194304,"worker memory");
 size_t row_bytes=n*40,block_bytes=rows*row_bytes;uint8_t *input=data+131072;
 read_block(argv[5],n,block,0,input+row_bytes,block_bytes);
 if(block==0)memcpy(input,input+row_bytes,row_bytes);
 else read_block(argv[5],n,block-1,(block_rows(n,block-1)-1)*row_bytes,input,row_bytes);
 if(block==23)memcpy(input+row_bytes+block_bytes,input+block_bytes,row_bytes);
 else read_block(argv[5],n,block+1,0,input+row_bytes+block_bytes,row_bytes);
 wasmtime_func_t function=exported(context,&instances[3],mode==0?"scan":mode==3?"initialize":"sweep",WASMTIME_EXTERN_FUNC).of.func;
 int count=mode==0||mode==3?2:5;
 wasmtime_val_t args[5]={{.kind=WASMTIME_I32,.of.i32=(int32_t)n},{.kind=WASMTIME_I32,.of.i32=(int32_t)(count==2?rows:start)},
  {.kind=WASMTIME_I32,.of.i32=(int32_t)rows},{.kind=WASMTIME_I32,.of.i32=mode==2},{.kind=WASMTIME_I64}};
 memcpy(&args[4].of.i64,&ratio,8);wasm_trap_t *trap=NULL;wasmtime_error_t *error=wasmtime_func_call(context,&function,args,(size_t)count,NULL,0,&trap);checked(error,trap);
 data=wasmtime_memory_data(context,&memory);char *p=name(argv[6],"block-",block,".meta");write_new(p,data,64);free(p);
 uint64_t status;memcpy(&status,data,8);
 if(mode!=0&&status==0){
  const uint8_t *output=data+2097152;size_t output_bytes=block_bytes;
  if(mode==1){for(size_t i=0;i<rows*n;i++)memcpy(input+i*32,output+i*40,32);output=input;output_bytes=rows*n*32;}
  p=name(argv[6],"block-",block,".bin");write_new(p,output,output_bytes);free(p);
  if(mode==1||(mode==2&&(block==0||block==23))){p=name(argv[6],"block-",block,".boundary");write_new(p,data+256,(mode==1?rows:n)*32);free(p);}
 }
 for(int i=0;i<3;i++){
  const char *counters[3]={"allocCount","releaseCount","freeCount"};
  for(int j=0;j<3;j++){wasmtime_global_t global=exported(context,&instances[i],counters[j],WASMTIME_EXTERN_GLOBAL).of.global;wasmtime_val_t value;wasmtime_global_get(context,&global,&value);require(value.kind==WASMTIME_I64&&value.of.i64==0,"unexpected kernel allocation");}
 }
 wasmtime_store_delete(store);wasm_engine_delete(engine);return 0;
}

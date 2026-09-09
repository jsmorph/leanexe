/* Host orchestration only. Numerical WASM contracts are proved separately. */
#include <wasm.h>
#include <wasmtime.h>
#include <float.h>
#include <inttypes.h>
#include <math.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
_Static_assert(sizeof(double)==8 && DBL_MANT_DIG==53 && DBL_MAX_EXP==1024, "binary64 host required");
typedef struct { wasm_engine_t *engine; wasmtime_store_t *store; wasmtime_context_t *context; wasmtime_instance_t instance; wasmtime_memory_t memory; } Runtime;
static void require(bool ok,const char *message){if(!ok){fprintf(stderr,"%s\n",message);exit(1);}}
static void checked(wasmtime_error_t *error,wasm_trap_t *trap){
 if(error){wasm_name_t m;wasmtime_error_message(error,&m);fprintf(stderr,"%.*s\n",(int)m.size,m.data);wasm_byte_vec_delete(&m);wasmtime_error_delete(error);exit(1);}
 if(trap){wasm_message_t m;wasm_trap_message(trap,&m);fprintf(stderr,"%.*s\n",(int)m.size,m.data);wasm_byte_vec_delete(&m);wasm_trap_delete(trap);exit(1);}
}
static wasmtime_extern_t exported(Runtime *r,const char *name,wasmtime_extern_kind_t kind){wasmtime_extern_t item;require(wasmtime_instance_export_get(r->context,&r->instance,name,strlen(name),&item),"missing export");require(item.kind==kind,"export type mismatch");return item;}
static void init(Runtime *r,const char *path){
 memset(r,0,sizeof(*r));FILE *f=fopen(path,"rb");require(f!=NULL,"cannot open WASM");require(fseek(f,0,SEEK_END)==0,"seek");long size=ftell(f);require(size>0,"empty WASM");rewind(f);uint8_t *bytes=malloc((size_t)size);require(bytes!=NULL,"allocation");require(fread(bytes,1,(size_t)size,f)==(size_t)size,"read WASM");fclose(f);
 r->engine=wasm_engine_new();require(r->engine!=NULL,"engine");wasmtime_module_t *module=NULL;checked(wasmtime_module_new(r->engine,bytes,(size_t)size,&module),NULL);free(bytes);
 r->store=wasmtime_store_new(r->engine,NULL,NULL);require(r->store!=NULL,"store");r->context=wasmtime_store_context(r->store);wasm_trap_t *trap=NULL;wasmtime_error_t *error=wasmtime_instance_new(r->context,module,NULL,0,&r->instance,&trap);checked(error,trap);wasmtime_module_delete(module);
 r->memory=exported(r,"memory",WASMTIME_EXTERN_MEMORY).of.memory;
 /* Deliberately call no runtime exports during instantiation. */
}
static void destroy(Runtime *r){wasmtime_store_delete(r->store);wasm_engine_delete(r->engine);}
static void call(Runtime *r,wasmtime_func_t *function,const uint64_t *inputs,size_t count,uint64_t *outputs,size_t results){
 require(count<=16&&results<=16,"call arity");wasmtime_val_t a[16],b[16];memset(a,0,sizeof a);memset(b,0,sizeof b);
 for(size_t i=0;i<count;i++){a[i].kind=WASMTIME_I64;memcpy(&a[i].of.i64,&inputs[i],8);}wasm_trap_t *trap=NULL;
 wasmtime_error_t *error=wasmtime_func_call(r->context,function,a,count,b,results,&trap);checked(error,trap);
 for(size_t i=0;i<results;i++){require(b[i].kind==WASMTIME_I64,"result type");memcpy(&outputs[i],&b[i].of.i64,8);}
}
static uint64_t global(Runtime *r,const char *name){wasmtime_global_t g=exported(r,name,WASMTIME_EXTERN_GLOBAL).of.global;wasmtime_val_t v;wasmtime_global_get(r->context,&g,&v);require(v.kind==WASMTIME_I64,"global type");uint64_t n;memcpy(&n,&v.of.i64,8);return n;}
static uint64_t bits(double x){uint64_t w;memcpy(&w,&x,8);return w;}
static double value(uint64_t w){double x;memcpy(&x,&w,8);return x;}
static double positive(double x){require(isfinite(x)&&x>0,"nonpositive/nonfinite host value");return x;}
static size_t memory_size(Runtime *r){return wasmtime_memory_data_size(r->context,&r->memory);}
static void put(Runtime *r,uint64_t address,uint64_t word){require(address<=memory_size(r)&&8<=memory_size(r)-address,"memory write");uint8_t *p=wasmtime_memory_data(r->context,&r->memory)+address;for(unsigned i=0;i<8;i++)p[i]=(uint8_t)(word>>(8*i));}
static uint64_t get(Runtime *r,uint64_t address){require(address<=memory_size(r)&&8<=memory_size(r)-address,"memory read");const uint8_t *p=wasmtime_memory_data(r->context,&r->memory)+address;uint64_t word=0;for(unsigned i=0;i<8;i++)word|=(uint64_t)p[i]<<(8*i);return word;}
static void array(Runtime *r,uint64_t pointer,const uint64_t *data,size_t size){put(r,pointer,size);for(size_t i=0;i<size;i++)put(r,pointer+8+8*i,data[i]);}
static void words(const uint64_t *data,size_t size){putchar('[');for(size_t i=0;i<size;i++)printf("%s\"%016" PRIx64 "\"",i?",":"",data[i]);putchar(']');}
static void sod(const char *scan_path,const char *step_path,size_t n,bool capture){
 require(n>=2&&n<=1000&&n%2==0,"cell count must be even,2..1000");Runtime scan,step;init(&scan,scan_path);init(&step,step_path);
 wasmtime_func_t scan_fn=exported(&scan,"maxSpeedCheckedBits",WASMTIME_EXTERN_FUNC).of.func,step_fn=exported(&step,"stepCheckedBits",WASMTIME_EXTERN_FUNC).of.func,reset_fn=exported(&step,"reset",WASMTIME_EXTERN_FUNC).of.func;
 size_t count=1+6*n,object_bytes=64+48*n,arena_end=4096+(n+6)*object_bytes,input_pointer=arena_end+48,required=input_pointer+8+24*n;
 if(memory_size(&step)<required){uint64_t previous=0;checked(wasmtime_memory_grow(step.context,&step.memory,(required+65535)/65536-memory_size(&step)/65536,&previous),NULL);}
 require(memory_size(&step)/65536<=65536,"memory page bound");
 uint64_t *grid=calloc(3*n,8),*next=calloc(3*n,8),*output=calloc(count,8);require(grid&&next&&output,"grid allocation");
 for(size_t i=0;i<n;i++){grid[3*i]=bits(i<n/2?1:.125);grid[3*i+2]=bits(i<n/2?2.5:.25);}
 printf("{\"layout\":{\"n\":%zu,\"inputPointer\":%zu,\"arenaEnd\":%zu,\"memoryBytes\":%zu}}\n",n,input_pointer,arena_end,memory_size(&step));
 double t=0,dx=1.0/(double)n,end=.2;size_t steps=0;
 while(t<end){
  require(steps<10000,"step budget");array(&scan,64,grid,3*n);uint64_t a[2]={64,0},result[2];call(&scan,&scan_fn,a,1,result,2);require(result[0]==0,"scan rejected");double alpha=positive(value(result[1])),dt=fmin(.45*dx/alpha,end-t),ratio=dt/dx;positive(dt);positive(ratio);require(t+dt>t&&t+dt<=end,"time progress");
  call(&step,&reset_fn,NULL,0,NULL,0);require(global(&step,"allocCount")==0&&global(&step,"releaseCount")==0&&global(&step,"freeCount")==0,"reset counters");array(&step,input_pointer,grid,3*n);a[0]=bits(ratio);a[1]=input_pointer;uint64_t root;call(&step,&step_fn,a,2,&root,1);
  require(root>=4096+48&&root<=arena_end&&8+8*count<=arena_end-root,"output arena");require(get(&step,root)==count,"output length");for(size_t j=0;j<count;j++)output[j]=get(&step,root+8+8*j);require(output[0]==0,"step rejected");
  double max_cfl=0,min_rho=INFINITY,min_p=INFINITY;
  for(size_t i=0;i<n;i++){const uint64_t *q=output+1+6*i;for(size_t k=0;k<6;k++)require(isfinite(value(q[k])),"nonfinite payload");positive(value(q[0]));positive(value(q[3]));positive(value(q[4]));positive(value(q[5]));require(value(q[5])<=.5,"CFL");max_cfl=fmax(max_cfl,value(q[5]));min_rho=fmin(min_rho,value(q[0]));min_p=fmin(min_p,value(q[3]));for(size_t k=0;k<3;k++)next[3*i+k]=q[k];}
  require(global(&step,"allocCount")==1+6*n&&global(&step,"releaseCount")==5*n+1&&global(&step,"freeCount")==5*n+1,"step counters");
  printf("{\"step\":%zu,\"t\":\"%016" PRIx64 "\",\"dt\":\"%016" PRIx64 "\",\"ratio\":\"%016" PRIx64 "\",\"alpha\":\"%016" PRIx64 "\",\"maxCfl\":\"%016" PRIx64 "\",\"minDensity\":\"%016" PRIx64 "\",\"minPressure\":\"%016" PRIx64 "\",\"boundaryWords\":",++steps,bits(t),bits(dt),bits(ratio),result[1],bits(max_cfl),bits(min_rho),bits(min_p));
  uint64_t boundary[6];memcpy(boundary,grid,24);memcpy(boundary+3,grid+3*n-3,24);words(boundary,6);if(capture){printf(",\"outputWords\":");words(output,count);}printf("}\n");
  uint64_t *old=grid;grid=next;next=old;t+=dt;
 }
 printf("{\"finalTime\":\"%016" PRIx64 "\",\"gridWords\":",bits(t));words(grid,3*n);printf("}\n");free(grid);free(next);free(output);destroy(&scan);destroy(&step);
}
int main(int argc,char **argv){require(argc==6&&strcmp(argv[1],"sod")==0,"usage: host sod scan.wasm step.wasm cells capture");char *end=NULL;long n=strtol(argv[4],&end,10);require(end&&*end==0&&n>=2&&n<=1000,"invalid cell count");require(strcmp(argv[5],"0")==0||strcmp(argv[5],"1")==0,"capture must be0/1");sod(argv[2],argv[3],(size_t)n,strcmp(argv[5],"1")==0);return 0;}

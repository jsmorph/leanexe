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
typedef struct { wasm_engine_t *engine; wasmtime_store_t *store; wasmtime_context_t *context; wasmtime_instance_t instance; wasmtime_memory_t memory; uint64_t calls; } Runtime;
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
 r->calls++; require(count<=16&&results<=16,"call arity");wasmtime_val_t a[16],b[16];memset(a,0,sizeof a);memset(b,0,sizeof b);
 for(size_t i=0;i<count;i++){a[i].kind=WASMTIME_I64;memcpy(&a[i].of.i64,&inputs[i],8);}wasm_trap_t *trap=NULL;
 wasmtime_error_t *error=wasmtime_func_call(r->context,function,a,count,b,results,&trap);checked(error,trap);
 for(size_t i=0;i<results;i++){require(b[i].kind==WASMTIME_I64,"result type");memcpy(&outputs[i],&b[i].of.i64,8);}
}
static uint64_t global(Runtime *r,const char *name){wasmtime_global_t g=exported(r,name,WASMTIME_EXTERN_GLOBAL).of.global;wasmtime_val_t v;wasmtime_global_get(r->context,&g,&v);require(v.kind==WASMTIME_I64,"global type");uint64_t n;memcpy(&n,&v.of.i64,8);return n;}
static uint64_t bits(double x){uint64_t w;memcpy(&w,&x,8);return w;}
static double value(uint64_t w){double x;memcpy(&x,&w,8);return x;}
static double positive(double x){require(isfinite(x)&&x>0,"nonpositive/nonfinite host value");return x;}

static void words(const uint64_t *data,size_t count) {
 putchar('['); for(size_t i=0;i<count;i++)printf("%s\"%016" PRIx64 "\"",i?",":"",data[i]); putchar(']');
}
static void doubles(const double *data,size_t count) {
 putchar('['); for(size_t i=0;i<count;i++)printf("%s\"%016" PRIx64 "\"",i?",":"",bits(data[i])); putchar(']');
}
static void oriented(const uint64_t *q,bool y,uint64_t *out) {
 out[0]=q[0]; out[1]=q[y?2:1]; out[2]=q[y?1:2]; out[3]=q[3];
}
static double scan(Runtime *r,wasmtime_func_t *fn,const uint64_t *grid,size_t n) {
 double maximum=0;
 for(size_t i=0;i<n*n;i++)for(unsigned axis=0;axis<2;axis++) {
  uint64_t q[4],out[8]; oriented(grid+4*i,axis!=0,q); call(r,fn,q,4,out,8);
  require(out[0]==0,"speed scan rejected a state"); maximum=fmax(maximum,positive(value(out[3])));
 }
 return positive(maximum);
}
typedef struct { double max_cfl,min_rho,min_p,max_velocity,min_energy_ratio; } Metrics;
static bool sweep(Runtime *r,wasmtime_func_t *fn,const uint64_t *grid,uint64_t *next,
                  uint64_t *pressures,size_t n,bool y,uint64_t ratio,Metrics *metrics) {
 for(size_t j=0;j<n;j++)for(size_t i=0;i<n;i++) {
  size_t index=j*n+i,previous=y?(j?j-1:0)*n+i:j*n+(i?i-1:0);
  size_t following=y?(j+1<n?j+1:n-1)*n+i:j*n+(i+1<n?i+1:n-1);
  uint64_t inputs[13],out[8]; inputs[0]=ratio;
  oriented(grid+4*previous,y,inputs+1); oriented(grid+4*index,y,inputs+5); oriented(grid+4*following,y,inputs+9);
  call(r,fn,inputs,13,out,8);
  if(out[0]!=0) { for(size_t k=1;k<8;k++)require(out[k]==0,"malformed cell rejection"); return false; }
  for(size_t k=1;k<8;k++)require(isfinite(value(out[k])),"nonfinite cell result");
  double rho=positive(value(out[1])),p=positive(value(out[5])),cfl=positive(value(out[7]));
  positive(value(out[6])); require(cfl<=.5,"cell CFL ceiling");
  double velocity=fmax(fabs(value(out[2])),fabs(value(out[3])))/rho,energy_ratio=value(out[4])/rho;
  require(velocity<=1&&energy_ratio>1,"updated sufficient domain");
  next[4*index]=out[1]; next[4*index+1]=out[y?3:2]; next[4*index+2]=out[y?2:3]; next[4*index+3]=out[4];
  pressures[index]=out[5]; metrics->max_cfl=fmax(metrics->max_cfl,cfl);
  metrics->min_rho=fmin(metrics->min_rho,rho); metrics->min_p=fmin(metrics->min_p,p);
  metrics->max_velocity=fmax(metrics->max_velocity,velocity); metrics->min_energy_ratio=fmin(metrics->min_energy_ratio,energy_ratio);
 }
 return true;
}
static void boundary(Runtime *r,wasmtime_func_t *fn,const uint64_t *grid,size_t n,bool y,double *difference) {
 for(size_t k=0;k<4;k++)difference[k]=0;
 for(size_t i=0;i<n;i++) {
  size_t lo=y?i:i*n,hi=y?(n-1)*n+i:i*n+n-1;
  uint64_t a[8],low[6],high[6]; oriented(grid+4*lo,y,a);memcpy(a+4,a,32);call(r,fn,a,8,low,6);
  oriented(grid+4*hi,y,a);memcpy(a+4,a,32);call(r,fn,a,8,high,6);
  require(low[0]==0&&high[0]==0,"boundary flux rejected");
  for(size_t k=0;k<4;k++){size_t slot=y&&k==1?3:y&&k==2?2:k+1;difference[k]+=value(high[slot])-value(low[slot]);require(isfinite(difference[k]),"boundary sum");}
 }
}
static void totals(const uint64_t *grid,size_t n,double *sum) {
 double correction[4]={0,0,0,0}; for(size_t k=0;k<4;k++)sum[k]=0;
 double area=(1.0/(double)n)*(1.0/(double)n);
 for(size_t i=0;i<n*n;i++)for(size_t k=0;k<4;k++) {
  double term=value(grid[4*i+k])*area-correction[k],next=sum[k]+term;
  correction[k]=(next-sum[k])-term;sum[k]=next;
 }
}
static void frame(size_t index,size_t step,double t,const uint64_t *grid,const uint64_t *pressure,size_t n) {
 printf("{\"kind\":\"frame\",\"index\":%zu,\"step\":%zu,\"t\":\"%016" PRIx64 "\",\"densityPressureWords\":[",index,step,bits(t));
 for(size_t i=0;i<n*n;i++)printf("%s\"%016" PRIx64 "\",\"%016" PRIx64 "\"",i?",":"",grid[4*i],pressure[i]);
 printf("]}\n");fflush(stdout);
}
static void simulate(const char *side_path,const char *flux_path,const char *cell_path,size_t n,size_t frames,bool blast) {
 Runtime side,flux,cell;init(&side,side_path);init(&flux,flux_path);init(&cell,cell_path);
 wasmtime_func_t side_fn=exported(&side,"sideCheckedBits",WASMTIME_EXTERN_FUNC).of.func;
 wasmtime_func_t flux_fn=exported(&flux,"fluxCheckedBits",WASMTIME_EXTERN_FUNC).of.func;
 wasmtime_func_t cell_fn=exported(&cell,"cellCheckedBits",WASMTIME_EXTERN_FUNC).of.func;
 uint64_t *grid=calloc(4*n*n,8),*middle=calloc(4*n*n,8),*next=calloc(4*n*n,8),*pressure=calloc(n*n,8);
 require(grid&&middle&&next&&pressure,"grid allocation");
 for(size_t j=0;j<n;j++)for(size_t i=0;i<n;i++) {
  size_t index=j*n+i;double rho=i<n/2?(j<n/2?.25:.4):(j<n/2?.7:1);
  double energy=2.5*rho;
  if(blast){int64_t x=2*(int64_t)i+1-(int64_t)n,y=2*(int64_t)j+1-(int64_t)n;rho=1;energy=16*(x*x+y*y)<(int64_t)(n*n)?5:2.5;}
  grid[4*index]=bits(rho);grid[4*index+3]=bits(energy);
  uint64_t out[8];call(&side,&side_fn,grid+4*index,4,out,8);require(out[0]==0,"initial state rejected");pressure[index]=out[2];
 }
 double end=blast?.15:.2;
 printf("{\"kind\":\"header\",\"scenario\":\"%s\",\"n\":%zu,\"frames\":%zu,\"endTime\":\"%016" PRIx64 "\",\"targetCfl\":\"%016" PRIx64 "\"}\n",blast?"circular-blast":"four-quadrants",n,frames,bits(end),bits(.4));
 frame(0,0,0,grid,pressure,n);
 double t=0,dx=1.0/(double)n,initial[4],balance[4]={0,0,0,0};totals(grid,n,initial);
 size_t steps=0,next_frame=1,retries=0;
 while(t<end) {
  require(steps<10000,"step budget");double alpha=scan(&side,&side_fn,grid,n),dt=fmin(.4*dx/alpha,end-t);size_t attempts=0;
  Metrics metrics;double ratio;
  for(;;) {
   require(attempts<24,"step rejection retry budget");positive(dt);ratio=positive(dt/dx);require(t+dt>t&&t+dt<=end,"time progress");
   metrics=(Metrics){0,INFINITY,INFINITY,0,INFINITY};
   if(sweep(&cell,&cell_fn,grid,middle,pressure,n,false,bits(ratio),&metrics)&&
      sweep(&cell,&cell_fn,middle,next,pressure,n,true,bits(ratio),&metrics))break;
   attempts++;retries++;dt*=.5;
  }
  double bx[4],by[4];boundary(&flux,&flux_fn,grid,n,false,bx);boundary(&flux,&flux_fn,middle,n,true,by);
  for(size_t k=0;k<4;k++)balance[k]+=dt*dx*(bx[k]+by[k]);
  printf("{\"kind\":\"step\",\"step\":%zu,\"t\":\"%016" PRIx64 "\",\"dt\":\"%016" PRIx64 "\",\"ratio\":\"%016" PRIx64 "\",\"alpha\":\"%016" PRIx64 "\",\"retries\":%zu,\"diagnostics\":",++steps,bits(t),bits(dt),bits(ratio),bits(alpha),attempts);
  double d[5]={metrics.max_cfl,metrics.min_rho,metrics.min_p,metrics.max_velocity,metrics.min_energy_ratio};doubles(d,5);
  printf(",\"boundaryX\":");doubles(bx,4);printf(",\"boundaryY\":");doubles(by,4);printf("}\n");
  uint64_t *old=grid;grid=next;next=old;t+=dt;
  while(next_frame<frames&&t>=end*(double)next_frame/(double)(frames-1))frame(next_frame++,steps,t,grid,pressure,n);
 }
 require(next_frame==frames,"missing frames");
 double final[4],residual[4];totals(grid,n,final);for(size_t k=0;k<4;k++)residual[k]=final[k]-initial[k]+balance[k];
 Runtime *runtime[3]={&side,&flux,&cell};for(size_t j=0;j<3;j++)require(global(runtime[j],"allocCount")==0&&global(runtime[j],"releaseCount")==0&&global(runtime[j],"freeCount")==0,"unexpected WASM allocation");
 printf("{\"kind\":\"final\",\"steps\":%zu,\"retries\":%zu,\"t\":\"%016" PRIx64 "\",\"calls\":[%" PRIu64 ",%" PRIu64 ",%" PRIu64 "],\"initialTotals\":",steps,retries,bits(t),side.calls,flux.calls,cell.calls);doubles(initial,4);
 printf(",\"finalTotals\":");doubles(final,4);printf(",\"boundaryIntegral\":");doubles(balance,4);printf(",\"balanceResidual\":");doubles(residual,4);
 printf(",\"gridWords\":");words(grid,4*n*n);printf("}\n");
 free(grid);free(middle);free(next);free(pressure);destroy(&side);destroy(&flux);destroy(&cell);
}
int main(int argc,char **argv) {
 require(argc==7,"usage: host scenario side.wasm flux.wasm cell.wasm mesh frames");
 require(strcmp(argv[1],"four-quadrants")==0||strcmp(argv[1],"circular-blast")==0,"unknown scenario");
 char *end=NULL;long n=strtol(argv[5],&end,10);require(end&&*end==0&&n>=4&&n<=384&&n%2==0,"mesh must be even,4..384");
 long frames=strtol(argv[6],&end,10);require(end&&*end==0&&frames>=2&&frames<=65,"frames must be2..65");
 simulate(argv[2],argv[3],argv[4],(size_t)n,(size_t)frames,strcmp(argv[1],"circular-blast")==0);return 0;
}

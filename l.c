#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <math.h>
#include "l.h"
int debug=1;

//toolkit
ZK ga(L s);
ZS ss(S s);

//errors
#define UE(x) {U(x);if(xt==-128); R x;}
ZK krr(S err) {K x=ga(0);xt=-128;x->s=ss(err);R x;}
//ZK orr(S err) {K x=ga(0);xt=-128;x->s=ss(err);R x;}

//buddy
#define EXP2(n)       (LOG2(np2((n))))
#define LV(s,ts)      (ts-((s)))
#define BL(lv)        ((lv))
#define SLV(lv,ts)    ((1ULL)<<((ts)-(lv)))
#define IX(p,lv,m,ts) (((G*)(p)-(G*)(m))/(SLV(lv,ts)))

L SIZE_EXP2=20ULL;
#define SIZE ((1ULL)<<SIZE_EXP2)

typedef struct b0 {struct b0* n;} *B;
typedef struct bl0 {J p;J n;} *BL;
V* mem;
L boff=32;
J lvs[320];

V* pa(L s) {V *x=mmap(0,s,PROT_READ|PROT_WRITE,MAP_ANONYMOUS|MAP_PRIVATE,-1,0);P(x!=MAP_FAILED,x);O("out of memory1");R 0;}

ZV bsl(I lv,V* p) {$(p==NULL, lvs[boff+lv]=-1, lvs[boff+lv]=(G*)p-(G*)mem);}
Z BL bgl(I lv) {J o=lvs[boff+lv]; if(o==-1)R NULL;R (BL)((G*)mem+o);}
ZJ p2o(V* p) {if(p==NULL)R -1;R (G*)p-(G*)mem;}
Z BL o2p(J o) {if(o==-1)R NULL;R (BL)((G*)mem+o);}

ZL np2(L v){v--;v|=v>>1;v|=v>>2;v|=v>>4;v|=v>>8;v|=v>>16;v|=v>>32;v++;R v;}
ZV binit() {DO(320,lvs[i]=-1);mem=malloc(SIZE);bsl(0,mem);bgl(0)->p=bgl(0)->n=-1;}
ZV* baddl(I n) {boff-=n;SIZE_EXP2+=n;mem=realloc(mem,SIZE);R (G*)mem+SLV(1,SIZE_EXP2);}
ZV* bal(I lv) {BL bl;
  if(lv<0){O("out of memory4 - %i\n",lv);R baddl(-lv+1);}
  if(lv==0&&bgl(lv)==NULL){O("out of memory3\n");R baddl(1);}
  if(bgl(lv)==NULL) {V* m;BL r;m=bal(lv-1),r=(BL)((G*)m+SLV(lv,SIZE_EXP2));r->n=r->p=-1,bsl(lv,r);R m;}
  bl=bgl(lv);
  LO("allocate: lv:%llu - ix:%llu - p:%p - pn:%p - pp:%p\n",lv,IX((V*)bl,lv,mem,SIZE_EXP2),bl,o2p(bl->n),o2p(bl->p));
  if(o2p(bl->n)){bsl(lv,o2p(bl->n));bgl(lv)->p=-1;}else bsl(lv, NULL);R bl;}
ZV* ba(C exp) {LO("requested:%llu - %llu\n",((1ULL)<<exp),LV(exp,SIZE_EXP2));R bal(LV(exp,SIZE_EXP2));}
ZV bfl(V* p,I lv) {L ix,size;G* buddy;BL tmp,bl;H found=0;
  ix=IX(p,lv,mem,SIZE_EXP2),size=SLV(lv,SIZE_EXP2);$((ix&1)==0, buddy=(G*)p+size, buddy=(G*)p-size);tmp=bgl(lv);
  O("%p\n",p);
  while(tmp) {found=(G*)tmp==buddy;if(found||tmp->n==-1)break;tmp=o2p(tmp->n);}
  if(found) {BL prev,next;
    bl=(BL)buddy,prev=o2p(bl->p),next=o2p(bl->n);if(prev)prev->n=p2o(next);if(next)next->p=p2o(prev);if(!prev)bsl(lv,next);
    LO("buddy:%p - lv:%p - p:%p - pn:%p - pp:%p\n",buddy,lvs[lv],p,next,prev);
    $((ix&1)==0,bfl(p, lv-1),bfl(buddy,lv-1));}
  else {bl=(BL)p,bl->p=p2o(tmp),bl->n=-1;$(tmp, tmp->n=p2o(bl), bsl(lv,bl));}
  LO("tmp:%p - lv:%p - p:%p - pn:%p - pp:%p\n",tmp,bgl(lv),p,o2p(bl->n),o2p(bl->p));}
ZV bf(V* p,L s) {bfl(p,LV(s,SIZE_EXP2));}

//
I sizes[10] = {sizeof(G*),sizeof(C),sizeof(G),sizeof(H),sizeof(I),sizeof(J),sizeof(E),sizeof(F),sizeof(C),sizeof(S)};
ZI sz(I t) {R sizes[abs(t)];}
K syms;

//memory
ZV* ma(C s) {V* v=ba(s);R v;}
ZV* ra(V* p, C os, C ns) {V* n=ma(ns);memmove(n,p,(1ULL)<<os);bf(p,os);R n;}

ZK r1(K x) {xr+=1;R x;}
ZK ga(L s) {C exp;K x;exp=EXP2(sizeof(struct k0)-1+s),x=r1(ma(exp)),x->m=exp;R x;}
ZK rga(K x, L n) {C exp;K z;exp=EXP2(sizeof(struct k0)-1+sz(xt)*n);$(exp>x->m,z=ra(x,x->m,exp),R x);z->m=exp; R z;}
ZV gf(K x) {bf(x,x->m);}
ZK r0(K x) {U(xr);xr--;if(xr==0){if(xt==0)DO(xn,r0(xK[i]));gf(x);R 0;};R x;}

//atoms
ZK ka(I t) {K x=ga(0);xt=t;R x;}
ZK kc(C c) {K x=ka(-KC);x->g=(C)c;R x;}
ZK ki(I i) {K x=ka(-KI);x->i=i;R x;}

//lists
ZK ktn(I t, L n) {K x;U(t>=0&&t<10);x=ga(sz(t)*n);xt=t,xn=n;R x;};
ZK ja(K* x, V* y) {*x=rga(*x,(*x)->n+1);memcpy(&kK(*x)[(*x)->n],y,sz((*x)->t));(*x)->n++;R *x;}
ZK js(K* x, S s) {I n=strlen(s);*x=rga(*x,(*x)->n+n);memcpy(&kG(*x)[(*x)->n],s,n);(*x)->n+=n;R *x;}
ZK jk(K* x, K y) {*x=rga(*x,(*x)->n+1);kK(*x)[(*x)->n]=r1(y);(*x)->n++;R *x;}
ZK jv(K* x, K y) {U((*x)->t==y->t);I n=(*x)->n;*x=rga(*x,n+y->n);memcpy(&kK(*x)[n],&kG(y),y->n*sz(y->t));(*x)->n=n+y->n;R *x;}

//tables
K xD(K cs, K rs) {K x=ktn(XD,2);kK(x)[0]=cs,kK(x)[1]=rs;R x;}
K xT(K d) {U(d->t==XT);K x=ga(0);xt=XT;xk=d;R x;}

//strings
ZK kpn(S s, I n) {K x=ktn(KC,n);memcpy((S)xG,s,n);R x;}
ZK kp(S s) {R kpn(s,strlen(s));}
ZS ss(S s) {K sym;DO(syms->n, sym=kK(syms)[i];P(strncmp((S)kG(sym),s,sym->n)==0,(S)kG(sym)));sym=kp(s);jk(&syms,sym);R (S)kG(sym);}

//symbols
ZK ks(S s) {K x=ka(-KS);x->s=ss(s);R x;}
ZV sinit() {syms=ktn(0,0);}

//kqueue/epoll


//parser
#define SB         0    /* blank                           */
#define SA         1    /* alphanumeric                    */
#define SO         2    /* other                           */
#define S9         3    /* digit                           */

#define EI         1    /* emit (b,i-1); b=.i              */
#define EN         2    /* b=.i                            */

#define CO         0    /* other                           */
#define CB         1    /* space or tab                    */
#define CA         2    /* letter                          */
#define C9         3    /* digit */
#define CC         4    /* colon */
#define CQ         5    /* quote */

typedef struct {C n,e;} ST;

Z ST state[4][4]={
  /*SB */ {{SO,EN},{SB,0 },{SA,EN},{S9,EN}},
  /*SA */ {{SO,EI},{SB,EI},{SA,0 },{S9,EI}},
  /*SO */ {{SO,EI},{SB,EI},{SA,EI},{S9,EI}},
  /*S9 */ {{SO,EI},{SB,EI},{SA,EI},{S9,0}},
};
/*          CO      CB      CA      C9   */

C ctype[256]={
 0,  0,  0,  0,  0,  0,  0,  0,  0, CB,  0,  0,  0,  0,  0,  0, /* 0                  */
 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0, /* 1                  */
CB,  0,  0,  0,  0,  0,  0, CQ,  0,  0,  0,  0,  0,  0,  0,  0, /* 2  !"#$%&'()*+,-./ */
C9, C9, C9, C9, C9, C9, C9, C9, C9, C9, CO,  0,  0,  0,  0,  0, /* 3 0123456789:;<=>? */
 0, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, /* 4 @ABCDEFGHIJKLMNO */
CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA,  0,  0,  0,  0, C9, /* 5 PQRSTUVWXYZ[\]^_ */
 0, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, /* 6 `abcdefghijklmno */
CA, CA, CA, CA, CA, CA, CA, CA, CA, CA, CA,  0,  0,  0,  0,  0, /* 7 pqrstuvwxyz{|}~  */
};

PV pst[256]={0};
I ttype[] = {0,0,0,0,INT,0,0,0,0,CHAR};
ZI pt(I t) {R ttype[abs(t)];}

K wordil(K x) {I i=0,s=0,e=0,b=0,ix=0;ST st;K ixs;K bs;
  ixs=ktn(KI,xn*2),bs=ktn(0,0);
  for(;i<xn;i++) {
    st=state[s][ctype[xG[i]]], s=st.n, e=st.e;
    if (e==EI) {kI(ixs)[ix]=b, kI(ixs)[ix+1]=i-1, b=i, ix+=2;}
    else if (e==EN) b=i;
    LO("i:%i - state: %i - effect:%i - b:%i - ix:%i - c:%c - %i\n",i,s,e,b,ix,xG[i],ctype[xG[i]]);
    if(s==SO&&SEMICOLON==xG[i]){LO("found ; adding block\n");ixs->n=ix;jk(&bs,ixs);r0(ixs);ixs=ktn(KI,xn*2);ix=0;}
  }
  r0(ixs);
  R bs;
}

#define V1M(name, op, XTYPE, ZTYPE, rt) K1(name) {K z;J size=sz(K ## XTYPE);  \
    if(x->t==-K ## XTYPE)R rt(op(*(XTYPE*)((G*)x+8))); \
    if(x->t==K ## XTYPE){z=ktn(K ## ZTYPE,x->n); \
      DO(x->n,*(ZTYPE*)(((G*)z)+16+size*i)=op(*(XTYPE*)(((G*)x)+16+size*i)));R z;} \
    R 0;                                                                \
}
#define V1F(name, op, XTYPE, ZTYPE, rt) K1(name) {K z; op;R z;}
#define V2(name, op, XTYPE, YTYPE, ZTYPE, rt) K2(name) {K z; \
    if(x->t==-K ## XTYPE&&y->t==-K ## YTYPE)R rt(*(XTYPE*)((G*)x+8) op *(XTYPE*)((G*)y+8)); \
    if(x->t==-K ## XTYPE&&y->t==K ## YTYPE){z=ktn(K ## ZTYPE,y->n); \
      DO(y->n,*(ZTYPE*)(((G*)z)+16+sz(K ## XTYPE)*i)=*(YTYPE*)(((G*)y)+16+sz(K ## XTYPE)*i) op *(XTYPE*)(((G*)x)+8));R z;} \
    if(x->t==K ## XTYPE&&y->t==-K ## YTYPE){z=ktn(K ## ZTYPE,x->n); \
      DO(x->n,*(ZTYPE*)(((G*)z)+16+sz(K ## XTYPE)*i)=*(XTYPE*)(((G*)x)+16+sz(K ## XTYPE)*i) op *(YTYPE*)(((G*)y)+8));R z;} \
    R 0;                                                                \
}

Z inline I neg(I i) {R -i;}

V1M(absoluteII,llabs,I,I,ki)
V1M(negateII,neg,I,I,ki)
V1F(headII,{$(xt>0, z=ki(kI(x)[0]), z=ki(x->i))},I,I,ki)

V2(plusIII,+,I,I,I,ki)
V2(minusIII,-,I,I,I,ki)
V2(mulIII,*,I,I,I,ki)

K2(plus)  {P(abs(xt)==KI&&abs(y->t)==KI, plusIII(x,y));R 0;}
K2(minus) {P(abs(xt)==KI&&abs(y->t)==KI, minusIII(x,y));R 0;}
K2(mul)   {P(abs(xt)==KI&&abs(y->t)==KI, mulIII(x,y));R 0;}

K2(absolute) {P(abs(xt)==KI, absoluteII(x));R 0;}
K2(negate) {P(abs(xt)==KI, negateII(x));R 0;}
K2(mul1) {P(abs(xt)==KI, headII(x));R 0;}

K2(intf) {LO("intf:%i\n",abs(x->i));K ls=ktn(KI,abs(x->i));I sign=SIGN(x->i);DO(abs(x->i), kI(ls)[i]=(i*sign));R ls;}
K3(dyad) {LO("dyad: %c\n",y->g);PV* v=&pst[y->g];K r=(*v->f2)(x,z);r0(x);r0(y);r0(z);R r;}
K3(monad) {LO("monad: %c\n",x->g);PV* v=&pst[x->g];K r=(*v->f1)(z);r0(z);R r;}
K3(is)   {Os(x);LO(" is %i\n", z->i);R 0;}

Z C spell[]={
  ':',  ';',  '+',   '-',    '!',      '*',
  ASGN, MARK, CPLUS, CMINUS, CESCMARK, CMUL
};
C spellin(C c) {DO(sizeof(spell)/2,P(spell[i]==c,spell[i+(sizeof(spell)/2)]));R 0;}
I ds(G id) {DO(sizeof(ctype), P(pst[id].id==id, pst[id].t));R 0;}
I qn(S tk, L n) {DO(n, P(tk[i]<'0'||(tk[i]>'9'&&tk[i]<'A')||(tk[i]>'Z'&&tk[i]<'a')||tk[i]>'z',0));R NOUN;}
I qv(C c) {I s;I ct;s=spellin(c);U(ct=ds(s));R ct;}
ZI pdef(C id, I t, K(*f1)(), K(*f2)(), I mr, I lr, I rr) {PV* v=&pst[(G)id];v->id=id,v->f1=f1,v->f2=f2,v->mr=mr,v->lr=lr,v->rr=rr,v->t=t;R 1;}

PT cases[] = {
  NOUN+NAME, ASGN,       VNA,  ANY,  is,    0, 2,
  MARK,      NOUN+NAME,  ASGN, VNA,  is,    1, 3,
  EDGE+VNA,  NOUN,       VERB, NOUN, dyad,  1, 3,
  EDGE+VNA,  VERB,       NOUN, ANY,  monad, 1, 2,
  EDGE+VNA,  ANY,        VERB, NOUN, monad, 2, 3
};

K enqueue(K s, K bs) {K res=ktn(0,0);
  DO(bs->n, K ixs=kK(bs)[i];DO(ixs->n, LO("%i",kI(ixs)[i]))LO("\n"););
  for(I b=0;b<bs->n;b++) {I top=0;SQ stack[8000]={0};K ixs=kK(bs)[b];
    for(I i=ixs->n-1;i>=0;i-=2) {S tk;L len=0;K r;I ct=-1, ws=4, ret=0;
      tk=(S)kC(s)+kI(ixs)[i-1], len=kI(ixs)[i]-kI(ixs)[i-1]+1, ct=ctype[tk[0]];
      LO("\nt: %i", ct);
      SW(ct) {
        CS(CO, {if((ct=qv(tk[0]))==0)ct=spellin(tk[0]);r=kc(tk[0]);})
        CS(CA, (ct=CHAR,    r=kpn(tk, len)))
        CS(C9, (ct=NUMERIC, r=ki(atoi(tk))))
        CD:    (ct=NOUN,    r=kpn(tk, len));
      }
      LO("\n");
      DO(len, LO("<%c,%i>", tk[i], r->i););
      LO(" - %i", ct);LO("\n");
      stack[top].t=ct, stack[top].e=r, top+=1;
      LO("top: %i", top);LO("\n");
      DO(top, LO("<%i,%i> - ", stack[i].t, stack[i].e->i))LO("\n");
      if(top<4&&i>1)continue;
      if(top<4)for(;top<4;top++)stack[top].t=MARK,stack[top].e=kp(";");
      DO(top, LO("<%i,%i> - ", stack[i].t, stack[i].e->i))LO("\n");
      do {
        for(I j=0;j<sizeof(cases)/sizeof(cases[0]);j++) {I cond=1;I start;I off;
          start=top-ws, off=ws-1;
          DO(ws, cond=cond&&(cases[j].c[i]&stack[start+off-i].t));
          if (cond) {I a,b,o=0;
            a=cases[j].b, b=cases[j].e;
            r=(*cases[j].f)(stack[start+off-a].e,stack[start+off-a-1].e,stack[start+off-b].e);
            if(r)stack[start+off-b].t=pt(r->t), stack[start+off-b].e=r, o=1;
            memmove(&stack[start+off-b+o], &stack[start+off-a+1], (top-a)*sizeof(stack[0]));
            top-=b-a+(o?0:1), ret=1;
            break;
          }
          ret=0;
        }
        if(ret&&i==1)for(;top<4;top++)stack[top].t=MARK,stack[top].e=kp(";");
      } while (i==1&&ret);
    }
    jk(&res,stack[0].e);
    DO(top, r0(stack[i].e))
  }
  r0(bs);r0(s);
  R res;
}

V show(K e) {
  if(e==0) R;
  if(e->t==-KI)O("%i\n", e->i);
  else if(e->t==KI){LO("show list of size:%llu\n",e->n);DO(e->n,O("%i ", kI(e)[i]));O("\n");};
}

V init() {
  pdef(CPLUS,VERB,absolute,plus,0,0,0);
  pdef(CMINUS,VERB,negate,minus,0,0,0);
  pdef(CMUL,VERB,mul1,mul,0,0,0);
  pdef(CESCMARK,VERB,intf,0,0,0,0);

  binit();
  sinit();
  O("allocated %llu\n",(1ULL)<<SIZE_EXP2);
}

V repl() {C str[8000]={0};
  O(">> ");
  while(fgets(str,8000,stdin)){K x, rs;
    x=kp(str);x->n--;js(&x,";");rs=enqueue(x,wordil(x));
    DO(rs->n, show(kK(rs)[i]));O(">> ");
    r0(rs);
  }
}

I main() {init();repl();
  K s1=kp("2+2+\n");
  js(&s1,";12");
  r0(s1);

}

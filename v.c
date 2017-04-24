#include "v.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

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
  /*SB */ {{SB,EN},{SB,0 },{SA,EN},{S9,EN}},
  /*SA */ {{SO,EI},{SB,EI},{SA,0 },{S9,EI}},
  /*SO */ {{SO,0 },{SB,EI},{SA,EI},{S9,EI}},
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

PV pst[256]={};
ZI sz(I t) {
  SW(abs(t)) {
      CS(KB, R sizeof(C))
      CS(KG, R sizeof(G))
      CS(KH, R sizeof(H))
      CS(KI, R sizeof(I))
      CS(KJ, R sizeof(J))
      CS(KE, R sizeof(E))
      CS(KF, R sizeof(F))
      CS(KC, R sizeof(C))
      CS(KS, R sizeof(S))
      CS(0,  R sizeof(struct k0))
  }
  R 0;
}
ZI pt(I t) {
  SW(abs(t)) {
    CS(KI, R INT)
    CS(KS, R CHAR)
  }
  R 0;
}

ZV* ma(J s) {V* p=malloc(s);memset(p,0,s);R p;}
ZV* ra(V* p, J s) {R realloc(p, s);}
ZK ga(J s) {R ma(sizeof(struct k0)-1+s);}
ZK rga(K x, J s) {R ra(x, sizeof(struct k0)+sz(xt)*xn-1+s);}
ZK ktn(I t, J n) {K x;U(t>=0&&t<10);x=ga(sz(t)*n), xt=t, xn=n;R x;};
ZK ks(S s) {I n=strlen(s);K x=ktn(KC,n);strncpy((S)xG,s,n);R x;}
ZK kc(C c) {K x=ga(0);x->t=-KC, x->g=(G)c;R x;}
ZK ki(I i) {K x=ga(0);x->t=-KI, x->i=i;R x;}
ZK ksn(S s, I n) {K x=ktn(KC,n);strncpy((S)xG,s,n);R x;}
V js(K* x, S s) {I n=strlen(s);*x=rga(*x, n);strncpy((S)&kG(*x)[(*x)->n],s,n);(*x)->n+=n;}
V jk(K* x, K y) {I s=sizeof(G*);*x=rga(*x,(*x)->n+1*s);memcpy(&kG(*x)[(*x)->n*s],(G*)&y,s);(*x)->n+=1;}

K1(wordil) {I i=0,s=0,e=0,b=0,wi=0;ST st;K w=ktn(KI,xn*2);
  for(;i<xn;i++) {
    st=state[s][ctype[(I)xG[i]]], s=st.n, e=st.e;
    if (e==1) {kI(w)[wi]=b, kI(w)[wi+1]=i-1, b=i, wi+=2;}
    else if (e==2) {b=i;}
    O("i:%i - state: %i - effect:%i - b:%i - wi:%i - c:%c - %i\n", i,s,e,b,wi,xG[i],ctype[xG[i]]);
  }
  kI(w)[wi]=b, kI(w)[wi+1]=i-1, w->n=wi+2;
  R w;
}

K3(is)   {Os(x);O(" is %i\n", z->i);R 0;}
K2(plus) {I a=0,b=0;I sum=x->i+y->i;O("sum = %i\n", sum);R ki(sum);}
K2(minus) {I a=0,b=0;I sub=x->i-y->i;O("sub = %i\n", sub);R ki(sub);}
K3(dyad) {O("dyad: %c\n",y->g);PV* v=&pst[y->g]; R (*v->f2)(x,z);}

Z C spell[]={
  ':',  ';',  '+', '-',
  ASGN, MARK, CPLUS, CMINUS
};
C spellin(C c) {DO(4,P(spell[i]==c,spell[i+4]));R 0;}
I ds(G id) {DO(sizeof(ctype), P(pst[id].id==id, pst[id].t));R 0;}
I qn(S tk, J n) {
  DO(n, P(tk[i]<'0'||(tk[i]>'9'&&tk[i]<'A')||(tk[i]>'Z'&&tk[i]<'a')||tk[i]>'z',0));
  R NOUN;
}
I qv(C c) {I s;I ct;s=spellin(c);U(ct=ds(s));R ct;}

ZI pdef(C id, I t, K(*f1)(), K(*f2)(), I mr, I lr, I rr) {
  PV* v=&pst[(G)id];
  v->id=id;
  v->f1=f1;
  v->f2=f2;
  v->mr=mr;
  v->lr=lr;
  v->rr=rr;
  v->t=t;
  R 1;
}

PT cases[] = {
  NOUN+NAME, ASGN,       VNA,  ANY,  is,   0, 2,
  MARK,      NOUN+NAME,  ASGN, VNA,  is,   1, 3,
  EDGE+VNA,  NOUN,       VERB, NOUN, dyad, 1, 3
};

V enqueue(K s, K w) {I top=0;SQ stack[8000]={};
  O("\n");
  for(I i=w->n-1;i>=0;i-=2) {
    S tk; J len=0; I ct=-1; K r;
    tk=(S)kC(s)+kI(w)[i-1], len=kI(w)[i]-kI(w)[i-1]+1;

    ct=ctype[tk[0]];
    O("\nt: %i", ct);

    SW(ct) {
      CS(CO, {if((ct=qv(tk[0]))==0)ct=spellin(tk[0]);r=kc(tk[0]);})
      CS(CA, (ct=CHAR,    r=ksn(tk, len)))
      CS(C9, (ct=NUMERIC, r=ki(atoi(tk))))
      CD:    (ct=NOUN,    r=ksn(tk, len));
    }

    O("\n");
    DO(len, O("<%c,%i>", tk[i], r->i););
    O(" - %i", ct);O("\n");

    stack[top].t=ct, stack[top].e=r, top+=1;

    O("top: %i", top);O("\n");
    DO(top, O("<%i,%i> - ", stack[i].t, stack[i].e->i))O("\n");
    if(top<4)continue;

    for(I j=0;j<sizeof(cases)/sizeof(cases[0]);j++) {I cond=1;I start;
      start=top-4;
      DO(4, cond=cond&&(cases[j].c[i]&stack[start+3-i].t));

      if (cond) {I a,b,o=0;
        a=cases[j].b, b=cases[j].e;
        r=(*cases[j].f)(stack[start+3-a].e,stack[start+3-a-1].e,stack[start+3-b].e);
        if(r)stack[start+3-b].t=pt(r->t), stack[start+3-b].e=r, o=1;
        memmove(&stack[start+3-b+o], &stack[start+3-a+1], (top-a)*sizeof(stack[0]));
        top-=b-a+(o?0:1);
        break;
      }
    }
  }
  free(w);
  free(s);
  DO(top, free(stack[i].e))
}

int main() {
  pdef(CPLUS,VERB,0,plus,0,0,0);
  pdef(CMINUS,VERB,0,minus,0,0,0);

  K x=ks("z:1-10+4;x:10-4+2-3;y:1;k:2+2;");
  //  js(&x, "z:1;");

  O("len:%lld\n", xn);

  OS(x);
  K w=wordil(x);

  O("%lld\n", w->n);
  DO(w->n, O("%i",kI(w)[i]));
  O("\n");
  enqueue(x,w);

  K y=ktn(0,0);
  K s=ks("ciao");
  K s1=ks("kek");
  jk(&y, s);
  jk(&y, s1);

  OS(kK(y)[0]);
  OS(kK(y)[1]);
}

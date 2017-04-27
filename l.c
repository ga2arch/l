#include "v.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
int debug=0;
//toolkit
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
      CS(0,  R sizeof(G*))
  }
  R 0;
}

// memory
ZV* ma(L s) {V* p=malloc(s);memset(p,0,s);R p;}
ZV* ra(V* p, L s) {R realloc(p, s);}
ZK ga(L s) {R ma(sizeof(struct k0)-1+s);}
ZK rga(K x, L n) {R ra(x, sizeof(struct k0)-1+sz(xt)*n);}

// atoms
ZK ka(I t) {K x=ga(0);xt=t;R x;}
ZK kc(C c) {K x=ka(-KC); x->g=(G)c;R x;}
ZK ki(I i) {K x=ka(-KI); x->i=i;R x;}

// lists
ZK ktn(I t, L n) {K x;U(t>=0&&t<10);x=ga(sz(t)*n),xt=t,xn=n;R x;};
ZK kpn(S s, I n) {K x=ktn(KC,n);memcpy((S)xG,s,n);R x;}
ZK kp(S s) {R kpn(s,strlen(s));}
ZK ja(K* x, V* y) {*x=rga(*x,(*x)->n+1);memcpy(&kK(*x)[(*x)->n],y,sz((*x)->t));(*x)->n++;R *x;}
ZK js(K* x, S s) {I n=strlen(s);*x=rga(*x,(*x)->n+n);memcpy(&kG(*x)[(*x)->n],s,n);(*x)->n+=n;R *x;}
ZK jk(K* x, K y) {*x=rga(*x,(*x)->n+1);memcpy(&kK(*x)[(*x)->n],&y,sizeof(G*));(*x)->n++;R *x;}
ZK jv(K* x, K y) {U((*x)->t==y->t);I n=0;n=(*x)->n;*x=rga(*x,n+y->n);memcpy(&kK(*x)[n],&kG(y),y->n*sz(y->t));(*x)->n=n+y->n;R *x;}

//tables


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
ZI pt(I t) {
  SW(abs(t)) {
    CS(KI, R INT)
    CS(KS, R CHAR)
  }
  R 0;
}

K wordil(K* px) {I i=0,s=0,e=0,b=0,ix=0;ST st;K x;K ixs;K bs;
  js(px, ";");x=*px;ixs=ktn(KI,xn*2),bs=ktn(0,0);
  for(;i<xn;i++) {
    st=state[s][ctype[xG[i]]], s=st.n, e=st.e;
    if (e==EI) {kI(ixs)[ix]=b, kI(ixs)[ix+1]=i-1, b=i, ix+=2;}
    else if (e==EN) b=i;
    LO("i:%i - state: %i - effect:%i - b:%i - ix:%i - c:%c - %i\n", i,s,e,b,ix,xG[i],ctype[xG[i]]);
    if(s==SO&&SEMICOLON==xG[i]){LO("found ; adding block\n");ixs->n=ix;jk(&bs, ixs);ixs=ktn(KI,xn*2);ix=0;}
  }
  R bs;
}

K3(is)   {Os(x);LO(" is %i\n", z->i);R 0;}
K2(plus) {I sum=x->i+y->i;LO("sum = %i\n", sum);R ki(sum);}
K2(minus) {I sub=x->i-y->i;LO("sub = %i\n", sub);R ki(sub);}
K3(dyad) {LO("dyad: %c\n",y->g);PV* v=&pst[y->g];R (*v->f2)(x,z);}

Z C spell[]={
  ':',  ';',  '+', '-',
  ASGN, MARK, CPLUS, CMINUS
};
C spellin(C c) {DO(4,P(spell[i]==c,spell[i+4]));R 0;}
I ds(G id) {DO(sizeof(ctype), P(pst[id].id==id, pst[id].t));R 0;}
I qn(S tk, L n) {DO(n, P(tk[i]<'0'||(tk[i]>'9'&&tk[i]<'A')||(tk[i]>'Z'&&tk[i]<'a')||tk[i]>'z',0));R NOUN;}
I qv(C c) {I s;I ct;s=spellin(c);U(ct=ds(s));R ct;}
ZI pdef(C id, I t, K(*f1)(), K(*f2)(), I mr, I lr, I rr) {PV* v;
  v=&pst[(G)id],v->id=id,v->f1=f1,v->f2=f2,v->mr=mr,v->lr=lr,v->rr=rr,v->t=t;R 1;
}

PT cases[] = {
  NOUN+NAME, ASGN,       VNA,  ANY,  is,   0, 2,
  MARK,      NOUN+NAME,  ASGN, VNA,  is,   1, 3,
  EDGE+VNA,  NOUN,       VERB, NOUN, dyad, 1, 3
};

K enqueue(K s, K bs) {
  LO("\n");
  for(I b=0;b<bs->n;b++) {I top=0;SQ stack[8000]={};K ixs=kK(bs)[b];
    for(I i=ixs->n-1;i>=0;i-=2) {
      S tk; L len=0; I ct=-1; K r;I ws=4;
      tk=(S)kC(s)+kI(ixs)[i-1], len=kI(ixs)[i]-kI(ixs)[i-1]+1;

      ct=ctype[tk[0]];
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

      for(I j=0;j<sizeof(cases)/sizeof(cases[0]);j++) {I cond=1;I start;I off;
        start=top-ws, off=ws-1;
        DO(ws, cond=cond&&(cases[j].c[i]&stack[start+off-i].t));

        if (cond) {I a,b,o=0;
          a=cases[j].b, b=cases[j].e;
          r=(*cases[j].f)(stack[start+off-a].e,stack[start+off-a-1].e,stack[start+off-b].e);
          if(r)stack[start+off-b].t=pt(r->t), stack[start+off-b].e=r, o=1;
          memmove(&stack[start+off-b+o], &stack[start+off-a+1], (top-a)*sizeof(stack[0]));
          top-=b-a+(o?0:1);
          break;
        }
      }

      if(i==1&&b==bs->n-1)R stack[0].e;};
  }
  R 0;
}


int main() {
  pdef(CPLUS,VERB,0,plus,0,0,0);
  pdef(CMINUS,VERB,0,minus,0,0,0);

  char str[8000]={0};
  while(fgets(str,8000,stdin)){
    K x=kp(str);K r=enqueue(x,wordil(&x));
    if(r!=0&&r->t==-KI)O("%i\n", r->i);
  }
}

/* int main() { */
/*   pdef(CPLUS,VERB,0,plus,0,0,0); */
/*   pdef(CMINUS,VERB,0,minus,0,0,0); */


/*   K x=kp("z:1+10+2+3;y:1;z:10-2+3-4;x:1;l:2;l"); */

/*   LO("len:%lld\n", xn); */

/*   OS(x); */
/*   K bs=wordil(&x); */

/*   LO("%lld\n", bs->n); */
/*   for(I i=0;i<bs->n;i++) { */
/*     K ixs=kK(bs)[i]; */
/*     DO(ixs->n, LO("%i",kI(ixs)[i]))LO("\n"); */
/*   } */

/*   LO("\n"); */
/*   enqueue(x,bs); */

/*   K y=ktn(0,0); */
/*   K z=ktn(0,0); */

/*   jk(&y, kp("ciao\0")); */
/*   jk(&z, kp("kek\0")); */
/*   jk(&z, kp("lol\0")); */

/*   jv(&y,z); */
/*   jk(&y,z); */

/*   LO("%s\n",kS(kK(y)[0])); */
/*   OS(kK(z)[0]); */
/*   OS(kK(kK(y)[3])[0]); */

/*   K j=ktn(KI, 0); */
/*   int i=5; */
/*   ja(&j, &i); */

/*   LO("- %i",kI(j)[0]); */
/* } */

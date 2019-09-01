fetch ../tst/prolegomena/appa.tst;

declare indconst x y z [NATNUM];
axiom E: x + suc(suc(zro)) = suc(suc(suc(suc(suc(zro)))));

declare funconst -(NATNUM,NATNUM) = NATNUM [inf = 450 455];
attach - to -;
axiom MINUS0R: forall n. n - zro = n;
axiom MINUS0L: forall n. zro - n = zro;
axiom MINUS: forall n m. suc(n) - suc(m) = n - m;
setbasicsimp TMINUS at facts {MINUS0R,MINUS0L,MINUS};

axiom THM1: forall p q m.(p=q imp p-m=q-m);
axiom THM2: forall p q m.(p+q)-m=p+(q-m);
theorem THM3 PLUS0;

setbasicsimp THM1 at facts {THM1};
setbasicsimp THM2 at facts {THM2};
setbasicsimp THM3 at facts {THM3};

alle THM1 x+suc(suc(zro)),suc(suc(suc(suc(suc(zro))))),suc(suc(zro));
theorem A 1;
rewrite A  by TMINUS uni THM2 uni THM3 uni LOGICTREE;
iffe 2 1;
impe 3 A;
impe 4 E;

namecontext OBJ;
MAKECONTEXT META;
SWITCHCONTEXT META;

DECLARE PREDCONST THEOREM 1;

DECLARE SORT TERM WFF FACT PREDCONST FUNCONST INDCONST;

DECREP TERM WFF FACT PREDCONST FUNCONST INDCONST;
REPRESENT {TERM} AS TERM;
REPRESENT {WFF} AS WFF;
REPRESENT {FACT} AS FACT;
REPRESENT {PREDCONST} AS PREDCONST;
REPRESENT {FUNCONST} AS FUNCONST;
REPRESENT {INDCONST} AS INDCONST;

MOREGENERAL TERM <INDCONST>;

DECLARE FUNCONST wffof (FACT)=WFF;
DECLARE FUNCONST lhs rhs (WFF)=TERM;
DECLARE FUNCONST larg rarg (TERM)=TERM;
ATTACH wffof TO [FACT=WFF] fact\-get\-wff;
ATTACH lhs TO [WFF=TERM] lhs;
ATTACH rhs TO [WFF=TERM] rhs;
DEFLAM larg (t) (CAR (appl\-get\-args t));
ATTACH larg TO [TERM=TERM] larg;
DEFLAM rarg (t) (CADR (appl\-get\-args t));
ATTACH rarg TO [TERM=TERM] rarg;

DECLARE FUNCONST mkimp (WFF WFF)=WFF;
ATTACH mkimp TO [WFF,WFF=WFF] mkimp;
DECLARE FUNCONST mktrmif (WFF TERM TERM)=TERM;
ATTACH mktrmif TO [WFF,TERM,TERM=TERM] mktrmif;

DECLARE FUNCONST pred2apply (PREDCONST TERM TERM)=WFF;
DECLARE INDCONST Equal < [PREDCONST];
MATTACH Equal dar [PREDCONST] OBJ::PREDCONST:=;
MATTACH < dar [PREDCONST] OBJ::PREDCONST:<;
ATTACH pred2apply TO [PREDCONST,TERM,TERM=WFF] predappl2\-mak;

DECLARE INDCONST zro [TERM];
MATTACH zro dar [INDCONST] OBJ::INDCONST:zro;
DECLARE FUNCONST fun1apply (FUNCONST TERM)=TERM;
DECLARE FUNCONST fun2apply (FUNCONST TERM TERM)=TERM;
DECLARE INDCONST suc + - [INDCONST];
MATTACH suc dar [FUNCONST] OBJ::FUNCONST:suc;
MATTACH + dar [FUNCONST] OBJ::FUNCONST:+;
MATTACH - dar [FUNCONST] OBJ::FUNCONST:-;
DEFLAM fun1apply (FUNSYM TERM1) (appl\-mak FUNSYM (LIST TERM1));
DEFLAM fun2apply (FUNSYM TERM1 TERM2) (appl\-mak FUNSYM (LIST TERM1 TERM2));
ATTACH fun2apply TO [FUNCONST,TERM,TERM=TERM] fun2apply;


DECLARE PREDCONST EQU 1;

DECLARE indvar x y z [TERM];
DECLARE indvar w r [WFF];
DECLARE indvar vl [FACT];

DECLARE PREDCONST LINEAREQ SUMEQ DIFFEQ 2;
AXIOM AX_LINEAREQ: forall w x.(LINEAREQ(w,x) iff (SUMEQ(w,x) or DIFFEQ(w,x)));
AXIOM AX_SUMEQ: forall w x.(SUMEQ(w,x) iff fun2apply(+,larg(lhs(w)),rarg(lhs(w)))=lhs(w));
AXIOM AX_DIFFEQ: forall w x.(DIFFEQ(w,x) iff fun2apply(-,larg(lhs(w)),rarg(lhs(w)))=lhs(w));
DECLARE FUNCONST solve (WFF TERM)=TERM;
AXIOM AX_SOLVE: forall w x.(solve(w, x)=
  trmif SUMEQ(w, x)
  then fun2apply(-,rhs(w),rarg(lhs(w)))
  else fun2apply(+,rhs(w),rarg(lhs(w))));
DECLARE FUNCONST ifSolvable (WFF TERM WFF)=WFF;
AXIOM AX_SOLVABLE: forall w x r.(ifSolvable(w, x, r)=
  trmif SUMEQ(w, x)
  then mkimp(pred2apply(<,rarg(lhs(w)),rhs(w)), r)
  else r);
SETBASICSIMP meta\-axioms at facts {AX_LINEAREQ,AX_SUMEQ,AX_DIFFEQ,AX_SOLVE,AX_SOLVABLE};
SETCOMPSIMP EVALSS AT LOGICTREE uni meta\-axioms;

AXIOM SOLVE_MINUS: forall w x.(THEOREM(pred2apply(Equal,x,fun2apply(+,rarg(lhs(w)),rhs(w)))));
AXIOM SOLVE_PLUS: forall w x.(THEOREM(mkimp(pred2apply(<,rarg(lhs(w)),rhs(w)), pred2apply(Equal,x,fun2apply(-,rhs(w),rarg(lhs(w)))))));

AXIOM SOLVE: forall w x.(LINEAREQ(w,x) imp THEOREM(ifSolvable(w,x,pred2apply(Equal,x,solve(w,x)))));

SWITCHCONTEXT OBJ;

reflect SOLVE (x-suc(suc(zro))=zro) x;
rewrite 6 by PEANO;
reflect SOLVE (y+suc(suc(zro))=suc(suc(suc(zro)))) y;
rewrite 8 by TMINUS;
reflect SOLVE (y-suc(suc(zro))=suc(suc(suc(zro)))) y;
rewrite 10 by PEANO;

fetch ../tst/prolegomena/appa.tst;

declare indconst x y z [NATNUM];
axiom E: x + suc(suc(zro)) = suc(suc(suc(suc(suc(zro)))));

declare funconst -(NATNUM,NATNUM) = NATNUM [inf = 450 455];
deflam minus (N M) (LET ((R (- N M))) (COND ((> R 0) R) (T 0)));
attach - to [NATNUM,NATNUM=NATNUM] minus;
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

theorem THMx 5;

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

DECLARE FUNCONST mainpred (WFF)=PREDCONST;
DECLARE FUNCONST pred2apply (PREDCONST TERM TERM)=WFF;
DECLARE INDCONST Equal [PREDCONST];
MATTACH Equal dar [PREDCONST] OBJ::PREDCONST:=;
DEFLAM mainpred (X) (AND (PREDAPPL X) (predappl\-get\-pred X));
ATTACH mainpred to [WFF=PREDCONST] mainpred;
ATTACH pred2apply TO [PREDCONST,TERM,TERM=WFF] predappl2\-mak;

DECLARE FUNCONST mainfun (TERM)=FUNCONST;
DECLARE FUNCONST fun1apply (FUNCONST TERM)=TERM;
DECLARE FUNCONST fun2apply (FUNCONST TERM TERM)=TERM;
DECLARE INDCONST zro [INDCONST];
DECLARE INDCONST suc + - [FUNCONST];
MATTACH zro dar [INDCONST] OBJ::INDCONST:zro;
MATTACH suc dar [FUNCONST] OBJ::FUNCONST:suc;
MATTACH + dar [FUNCONST] OBJ::FUNCONST:+;
MATTACH - dar [FUNCONST] OBJ::FUNCONST:-;
DEFLAM mainfun (X) (AND (FUNAPPL X) (funappl\-get\-fun X));
ATTACH mainfun to [TERM=FUNCONST] mainfun;
ATTACH fun1apply TO [FUNCONST,TERM=TERM] funappl1\-mak;
ATTACH fun2apply TO [FUNCONST,TERM,TERM=TERM] funappl2\-mak;


DECLARE indvar x y z [TERM];
DECLARE indvar w [WFF];
DECLARE indvar op [FUNCONST];

DECLARE PREDCONST NUMERAL 1;
DECLARE PREDCONST numeral 3;
DEFLAM numeral (X zro suc) (OR (EQ X zro) (AND (FUNAPPL X) (EQ (funappl\-get\-fun X) suc) (numeral (funappl1\-get\-arg X) zro suc)));
ATTACH numeral TO [TERM,INDCONST,FUNCONST] numeral;
AXIOM AX_NUMERAL: forall x.(NUMERAL(x) iff numeral(x,zro,suc));

DECLARE PREDCONST LEQ 2;
DEFLAM leq (X Y) (COND ((AND (FUNAPPL X) (FUNAPPL Y)) (lt (CADR X) (CADR Y))) ((FUNAPPL Y) T) ((FUNAPPL X) F) (T T));
ATTACH LEQ to [TERM,TERM] leq;

DECLARE FUNCONST PLUS MINUS (TERM TERM)=TERM;
DEFLAM plus  (X Y) (IF (FUNAPPL Y) (LIST (CAR Y) (plus X (CADR Y))) X);
DEFLAM minus (X Y) (IF (FUNAPPL X) (IF (FUNAPPL Y) (minus (CADR X) (CADR Y)) X) X);
ATTACH PLUS TO [TERM,TERM=TERM] plus;
ATTACH MINUS TO [TERM,TERM=TERM] minus;

DECLARE PREDCONST EQU 1;
DECLARE PREDCONST SOLVE_THM LINEAREQ SUMEQ DIFFEQ 2;
AXIOM AX_LINEAREQ: forall w x.(LINEAREQ(w,x) iff (
  EQU(w) and
  (SUMEQ(w,x) or DIFFEQ(w,x)) and
  larg(lhs(w))=x and
  (NUMERAL(rarg(lhs(w))) and NUMERAL(rhs(w))) and
  (SUMEQ(w,x) imp LEQ(larg(lhs(w)),rhs(w)))));
AXIOM AX_EQU: forall w.(EQU(w) iff mainpred(w)=Equal);
AXIOM AX_SUMEQ: forall w x.(SUMEQ(w,x) iff mainfun(lhs(w))=+);
AXIOM AX_DIFFEQ: forall w x.(DIFFEQ(w,x) iff mainfun(lhs(w))=-);
DECLARE FUNCONST solve (WFF TERM)=TERM;
AXIOM AX_SOLVE: forall w x.(solve(w, x)=
  trmif SUMEQ(w, x)
  then MINUS(rhs(w),rarg(lhs(w)))
  else PLUS(rhs(w),rarg(lhs(w))));

AXIOM AX_SOLVE_THM: forall w x.(SOLVE_THM(w,x) iff (LINEAREQ(w,x) imp THEOREM(pred2apply(Equal,x,solve(w,x)))));

AXIOM SOLVE: forall w x.SOLVE_THM(w,x);

AXIOM SOLVE_MINUS_LINEAREQ: forall x y z.SOLVE_THM(pred2apply(Equal,fun2apply(-,x,y),z),x);

SETBASICSIMP meta\-axioms at facts {AX_LINEAREQ,AX_EQU,AX_SUMEQ,AX_DIFFEQ,AX_SOLVE,AX_SOLVE_THM,AX_NUMERAL};
SETCOMPSIMP EVALSS AT LOGICTREE uni meta\-axioms;

SWITCHCONTEXT OBJ;

reflect SOLVE (y-suc(suc(zro))=zro) y;

reflect SOLVE (x+suc(suc(zro))=suc(suc(suc(suc(suc(zro)))))) x;

reflect SOLVE_MINUS_LINEAREQ z suc(suc(zro)) suc(suc(suc(zro)));

show axiom;

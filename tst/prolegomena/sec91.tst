fetch ../tst/prolegomena/appa.tst;

declare indconst x [NATNUM];
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

DECLARE SORT WFF TERM PREDCONST FUNCONST;

DECLARE PREDCONST THEOREM 1;

DECREP WFF TERM PREDCONST FUNCONST;
REPRESENT {WFF} AS WFF;
REPRESENT {TERM} AS TERM;
REPRESENT {PREDCONST} AS PREDCONST;
REPRESENT {FUNCONST} AS FUNCONST;

DECLARE FUNCONST pred2apply (PREDCONST TERM TERM)=WFF;
DECLARE INDCONST Equal  [PREDCONST];
MATTACH Equal     dar [PREDCONST] OBJ::PREDCONST:=;
ATTACH pred2apply  TO  [PREDCONST,TERM,TERM=WFF] predappl2\-mak;

DECLARE FUNCONST lhs rhs  (WFF)=TERM;

ATTACH lhs	TO [WFF=TERM] lhs;
ATTACH rhs	TO [WFF=TERM] rhs;

DECLARE FUNCONST fun2apply (FUNCONST TERM TERM)=TERM;
DECLARE INDCONST + [INDCONST];
MATTACH + dar [FUNCONST] OBJ::FUNCONST:+;
DEFLAM fun2apply (FUNSYM TERM1 TERM2) (appl\-mak FUNSYM (LIST TERM1 TERM2));
ATTACH fun2apply TO [FUNCONST,TERM,TERM=TERM] fun2apply;

DECLARE indvar x y z [TERM];

AXIOM SOLVE_MINUS: forall x y z.(THEOREM(pred2apply(Equal,x,fun2apply(+,y,z))));

SWITCHCONTEXT OBJ;
REFLECT SOLVE_MINUS x suc(suc(zro)) zro;

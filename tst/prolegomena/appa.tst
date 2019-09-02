declare sort NATNUM;
declare indvar n m p q [NATNUM];
declare indconst zro [NATNUM];
declare funconst suc prd (NATNUM) = NATNUM;
declare funconst +(NATNUM,NATNUM) = NATNUM [inf = 450 455];
declare funconst *(NATNUM,NATNUM) = NATNUM [inf = 550 555];
declare predconst < 2 [inf];
declare predpar P 1;

axiom ONEONE: forall n m.(suc(n)=suc(m) imp n=m);
axiom SUCC1: forall n.not(zro=suc(n));
axiom SUCC2: forall n.not(zro=n) imp exists m.n=suc(m);
axiom PLUS0: forall n. n + zro = n;
axiom PLUS: forall n m. n+suc(m)=suc(n+m);
axiom TIMES0: forall n. n * zro = zro;
axiom TIMES: forall n m. n*suc(m)=(n*m)+n;

axiom INDUCT: P(zro) and forall n.(P(n) imp P(suc(n))) imp forall n.P(n);

setbasicsimp PEANO at facts {ONEONE,SUCC1,SUCC2,PLUS0,PLUS,TIMES0,TIMES};

decrep NATNUM;
represent {NATNUM} as NATNUM;
attach zro to [NATNUM] 0;
attach suc to [NATNUM=NATNUM] ADD1;
deflam prd(x) (COND ((> x 0) (SUB1 x)) (T 0));
attach prd to [NATNUM=NATNUM] prd;
attach + to [NATNUM,NATNUM=NATNUM] +;
attach * to [NATNUM,NATNUM=NATNUM] *;
attach < to [NATNUM,NATNUM] <;

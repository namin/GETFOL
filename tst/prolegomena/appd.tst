fetch ../tst/prolegomena/appa.tst;
fetch ../tst/prolegomena/appb.tst;

declare funconst length (UNIVERSALREP)=NATNUM;
attach cons to CONS;
attach car to CAR;
attach cdr to CDR;
attach nil to NIL;
attach length to [UNIVERSALREP=NATNUM] LENGTH;

simplify length(cons(nil, cons(nil, nil)))=suc(suc(zro));

simplify zro < prd(suc(suc(zro)));
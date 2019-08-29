fetch ../tst/prolegomena/appa.tst;
fetch ../tst/prolegomena/appb.tst;

declare funconst length 1;
attach cons to CONS;
attach car to CAR;
attach cdr to CDR;
attach nil to NIL;
attach length to LENGTH;

simplify length(cons(zro, cons(suc(zro), nil)))=suc(suc(zro));

simplify zro < prd(suc(suc(zro)));
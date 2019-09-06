fetch ../tst/prolegomena/appa.tst;
fetch ../tst/prolegomena/appb.tst;

declare funconst length (List)=NATNUM;
attach cons to [Sexp,Sexp=Sexp] CONS;
attach car to [Sexp=Sexp] CAR;
attach cdr to [Sexp=Sexp] CDR;
attach nil to [Sexp] NIL;
attach length to [Sexp=NATNUM] LENGTH;

simplify length(cons(nil, cons(nil, nil)))=suc(suc(zro));

simplify zro < prd(suc(suc(zro)));
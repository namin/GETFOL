declare sort Sexp Lisp Null Atom;
declare indvar x y z [Sexp];
declare indvar u v w [List];
declare indconst nil [Null];

declare funconst car cdr 1;
declare funconst cons(Sexp,List)=List;
declare funconst rev 1;
declare funconst @ 2 [inf];

moregeneral Sexp < List, Atom, Null >;
moregeneral List < Null >;

DECREP SEXPREP;
represent {Sexp} as SEXPREP;

axiom CAR: forall x y. car(cons(x,y))=x;
axiom CDR: forall x y. cdr(cons(x,y))=y;
axiom CONS: forall x y. not(Null(cons(x,y)));

setbasicsimp Basic at facts {CAR,CDR,CONS};

axiom REV: forall u.(rev(u) = trmif Null(u) then u else rev(cdr(u)) @ cons(car(u),nil));
axiom APPEND: forall u v.(u@v = trmif Null(u) then v else cons(car(u),cdr(u)@v));

setbasicsimp Funs at facts {REV,APPEND};

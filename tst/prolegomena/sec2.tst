declare indconst Socrates;
declare predconst Mortal Man 1;
declare indvar x;

assume (Man(Socrates) and (forall x. (Man(x) imp Mortal(x))));

taut forall x. (Man(x) imp Mortal(x)) by 1;
alle 2 Socrates;
taut Mortal(Socrates) by 1 3;

impi 1 imp 4;

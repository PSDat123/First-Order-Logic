:- discontiguous male/1, female/1, parent/2, married/2, divorced/2.
% Queen Elizabeth II and Prince Phillip
male('Prince Phillip').
female('Queen Elizabeth II').
married('Prince Phillip', 'Queen Elizabeth II').
married('Queen Elizabeth II', 'Prince Phillip').
parent('Queen Elizabeth II','Prince Charles').
parent('Prince Phillip', 'Prince Charles').
parent('Queen Elizabeth II','Princess Anne').
parent('Prince Phillip', 'Princess Anne').
parent('Queen Elizabeth II','Prince Andrew').
parent('Prince Phillip', 'Prince Andrew').
parent('Queen Elizabeth II','Prince Edward').
parent('Prince Phillip', 'Prince Edward').

% Prince Charles and Princess Diana and Camilla Parker Bowles
male('Prince Charles').
female('Princess Diana').
female('Camilla Parker Bowles').
divorced('Princess Diana', 'Prince Charles').
divorced('Prince Charles', 'Princess Diana').
married('Prince Charles', 'Camilla Parker Bowles').
married('Camilla Parker Bowles', 'Prince Charles').
parent('Prince Charles', 'Prince William').
parent('Princess Diana', 'Prince William').
parent('Prince Charles', 'Prince Harry').
parent('Princess Diana', 'Prince Harry').

% Princess Anne and Captain Mark Phillips and Timothy Laurence
female('Princess Anne').
male('Captain Mark Phillips').
male('Timothy Laurence').
divorced('Princess Anne', 'Captain Mark Phillips').
divorced('Captain Mark Phillips', 'Princess Anne').
married('Princess Anne', 'Timothy Laurence').
married('Timothy Laurence', 'Princess Anne').
parent('Princess Anne', 'Peter Phillips').
parent('Captain Mark Phillips', 'Peter Phillips').
parent('Princess Anne', 'Zara Phillips').
parent('Captain Mark Phillips', 'Zara Phillips').

% Prince Andrew and Sarah Ferguson
male('Prince Andrew').
female('Sarah Ferguson').
divorce('Prince Andrew', 'Sarah Ferguson').
divorce('Sarah Ferguson', 'Prince Andrew').
parent('Prince Andrew', 'Princess Beatrice').
parent('Sarah Ferguson', 'Princess Beatrice').
parent('Prince Andrew', 'Princess Eugenie').
parent('Sarah Ferguson', 'Princess Eugenie').

% Prince Edward and Sophie Rhys-jones
male('Prince Edward').
female('Sophie Rhys-jones').
married('Prince Edward', 'Sophie Rhys-jones').
married('Sophie Rhys-jones', 'Prince Edward').
parent('Prince Edward', 'James, Viscount Severn').
parent('Sophie Rhys-jones', 'James, Viscount Severn').
parent('Prince Edward', 'Lady Louise Mountbatten-Windsor').
parent('Sophie Rhys-jones', 'Lady Louise Mountbatten-Windsor').

% Prince William and Kate Middleton
male('Prince William').
female('Kate Middleton').
married('Kate Middleton', 'Prince William').
married('Prince William', 'Kate Middleton').
parent('Kate Middleton', 'Prince George').
parent('Prince William', 'Prince George').
parent('Kate Middleton', 'Princess Charlotte').
parent('Prince William', 'Princess Charlotte').

% Prince Harry
male('Prince Harry').

% Peter Phillips and Autumn Kelly
male('Peter Phillips').
female('Autumn Kelly').
married('Peter Phillips', 'Autumn Kelly').
married('Autumn Kelly', 'Peter Phillips').
parent('Peter Phillips', 'Savannah Phillips').
parent('Autumn Kelly', 'Savannah Phillips').
parent('Peter Phillips', 'Isla Phillips').
parent('Autumn Kelly', 'Isla Phillips').

% Zara Phillips and Mike Tindall
male('Mike Tindall').
female('Zara Phillips').
married('Zara Phillips', 'Mike Tindall').
married('Mike Tindall','Zara Phillips').
parent('Mike Tindall', 'Mia Grace Tindall').
parent('Zara Phillips', 'Mia Grace Tindall').

% Princess Beatrice
female('Princess Beatrice').

% Princess Eugenie
female('Princess Eugenie').

% James, Viscount Severn
male('James, Viscount Severn').

% Lady Louise Mountbatten-Windsor
female('Lady Louise Mountbatten-Windsor').

% Prince George
male('Prince George').

% Princess Charlotte
female('Princess Charlotte').

% Savannah Phillips
female('Savannah Phillips').

% Isla Phillips
female('Isla Phillips').

% Mia Grace Tindall
female('Mia Grace Tindall').


%
% Addition predicates
%

husband(Person, Wife) :- male(Person), married(Person, Wife).
wife(Person, Husband) :- female(Person), married(Person, Husband).

father(Parent, Child) :- male(Parent), parent(Parent, Child).
mother(Parent, Child) :- female(Parent), parent(Parent, Child).
child(Child, Parent) :- parent(Parent, Child).
son(Child, Parent) :- male(Child), child(Child, Parent).
daughter(Child, Parent) :- female(Child), child(Child, Parent).

grandparent(GP, GC) :- parent(GP, Parent), parent(Parent, GC).
grandmother(GM, GC) :- female(GM), grandparent(GM, GC).
grandfather(GF, GC) :- male(GF), grandparent(GF, GC).

grandchild(GC, GP) :- grandparent(GP, GC).
grandson(GS, GP) :- male(GS), grandchild(GS, GP).
granddaughter(GD, GP) :- female(GD), grandchild(GD, GP).

sibling(Person1, Person2) :- father(Father, Person1), father(Father, Person2), mother(Mother, Person1), mother(Mother, Person2), Person1 \= Person2.
brother(Person, Sibling) :- male(Person), sibling(Person, Sibling).
sister(Person, Sibling) :- female(Person), sibling(Person, Sibling).

aunt(Person, NieceNephew) :-
    parent(Parent, NieceNephew),
    (sister(Person, Parent); (brother(Uncle, Parent), wife(Person, Uncle))).

uncle(Person, NieceNephew) :-
    parent(Parent, NieceNephew),
    (brother(Person, Parent); (sister(Aunt, Parent), husband(Person, Aunt))).

niece(Person, AuntUncle) :-
    female(Person),
    (aunt(AuntUncle, Person); uncle(AuntUncle, Person)).

nephew(Person, AuntUncle) :-
    male(Person),
    (aunt(AuntUncle, Person); uncle(AuntUncle, Person)).

% Util functions
list_parents(C, L) :- setof(Parent, parent(Parent, C), L).
list_childs(P, L) :- setof(Child, child(Child, P), L).

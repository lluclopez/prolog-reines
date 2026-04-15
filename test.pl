%%%%%%%%%%%%
% sat(F,I,M)
% si F es satisfactible, M sera el model de F afegit a la interpretació I (a la primera crida I sera buida).
% Assumim invariant que no hi ha literals repetits a les clausules ni la clausula buida inicialment.

sat([],I,I):- write('SAT!!'),nl,!.
sat(CNF,I,M):-
% Ha de triar un literal d’una clausula unitaria, si no n’hi ha cap, llavors un literal pendent qualsevol.
decideix(CNF,Lit),

% Simplifica la CNF amb el Lit triat (compte pq pot fallar, es a dir si troba la clausula buida fallara i fara backtraking).
simplif(Lit,CNF,CNFS),

% crida recursiva amb la CNF i la interpretacio actualitzada
sat(CNFS,[Lit|I],M).


% Cas base
sat(CNF,I,M):-
    decideix(CNF,Lit),
    Lit2 is -Lit,
    simplif(Lit2,CNF,CNFS),
    sat(CNFS,[Lit2|I],M).

%%%%%%%%%%%%%%%%%%
% decideix(F, Lit)
% Donat una CNF,
% -> el segon parametre sera un literal de CNF
%  - si hi ha una clausula unitaria sera aquest literal, sino
%  - un qualsevol o el seu negat.
% ...
decideix(CNF,Lit):-
    member([Lit],CNF), !.

decideix(CNF,Lit):-
    member(Cl,CNF),
    member(Lit,Cl), !.

%%%%%%%%%%%%%%%%%%%%%
% simlipf(Lit, F, FS)
% Donat un literal Lit i una CNF,
% -> el tercer parametre sera la CNF que ens han donat simplificada:
%  - sense les clausules que tenen lit
%  - treient -Lit de les clausules on hi es, si apareix la clausula buida fallara.
% ...
simplif(_,[],[]).

simplif(Lit,[Cl|Cls],Res):-
    member(Lit,Cl), !,
    simplif(Lit,Cls,Res).

simplif(Lit,[Cl|Cls],[Cl2|Res]):-
    LitNeg is -Lit,
    elimina(LitNeg,Cl,Cl2),
    Cl2 \= [],
    simplif(Lit,Cls,Res).

% Auxiliar
% elimina(X,L,R)
elimina(_,[],[]).

elimina(X,[X|Xs],R):- !,
    elimina(X,Xs,R).

elimina(X,[Y|Ys],[Y|R]):-
    elimina(X,Ys,R).










fesTauler(N,PI,PP,V,I):-
    llista(1,N*N,Vi),
    trosseja(Vi,N,V),
    fixa(PI,N,R1),
    prohibeix(PP,N,R2),
    append(R1,R2,I).


resol:-
    write('Mida del tauler? '), read(N),
    write('Posicions inicials? '), read(I),
    write('Posicions prohibides? '), read(P),

    fesTauler(N,I,P,V,Ini),

    write('Variables tauler: '), write(V), nl,
    write('CNF inicial: '), write(Ini), nl,

    minimNReines(V,FN),
    noAmenacesFiles(V,CNFfiles),
    %noAmenacesColumnes(V,CNFcolumnes),
	CNFcolumnes = [],
    %noAmenacesDiagonals(N,CNFdiagonals),
	CNFdiagonals = [],

    append(Ini,FN,T1),
    append(T1,CNFfiles,T2),
    append(T2,CNFcolumnes,T3),
    append(T3,CNFdiagonals,CNF),

    write('CNF total: '), write(CNF), nl,

    sat(CNF,[],M),

    write('Model: '), write(M), nl,

    literalsPositius(M,Pos),
    mostraTauler(N,Pos).


literalsPositius([],[]).
literalsPositius([X|Xs],[X|R]):- X > 0, !, literalsPositius(Xs,R).
literalsPositius([_|Xs],R):- literalsPositius(Xs,R).


%%%%%%%%%%%%%%%%%%%
% comaminimUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a minim una sigui certa.
% ...
comaminimUn(L,[L]).


%%%%%%%%%%%%%%%%%%%
% comamoltUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a molt una sigui certa.
% ...
comamoltUn([],[]).
comamoltUn([L|Ls],Res):-
	comamoltUn_aux(L,Ls,R),
	comamoltUn(Ls,CNF),
	append(R,CNF,Res).

comamoltUn_aux(L,[],[]).
comamoltUn_aux(L,[Ls|Lss],[[-L,-Ls]|R]):-
	comamoltUn_aux(L,Lss,R).
	


%%%%%%%%%%%%%%%%%%%
% exactamentUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que exactament una sigui certa.
% ...
exactamentUn(L,CNF):-
	comaminimUn(L,R1),
	comamoltUn(L,R2),
	append(R1,R2,CNF).



%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesFiles(+V,F)
% donada la matriu de variables,
% -> F sera la CNF que codifiqui que no samenecen les reines de les mateixes files
% ...
noAmenacesFiles([],[]).
noAmenacesFiles([L|Ls],R):-
	exactamentUn(L,CNF),
	noAmenacesFiles(Ls,F),
	append(CNF,F,R).
%noAmenacesFiles(V,F) → cada fila: exactamentUn/2


%%%%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesColumnes(+V,C)
% donada la matriu de variables,
% -> C sera la CNF que codifiqui que no samenecen les reines de les mateixes columnes
% ...
noAmenacesColumnes([],[]).
noAmenacesColumnes(V,[CNF|F]):-
	noAmenacesColumnes_aux(V,[L|Ls]),
	exactamentUn(L,CNF),
	noAmenacesColumnes(Ls,F).


%noAmenacesColumnes_aux(+V,-L)
noAmenacesColumnes_aux([],[]).
%noAmenacesColumnes_aux([L|Ls],[T|R]):-
	% length de L
	% I is L
	%append 

%noAmenacesColumnes(V,C) → cada columna: exactamentUn/2






%%%%%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesDiagonals(+N,C)
% donada la mida del tauler,
% -> D sera la CNF que codifiqui que no samenecen les reines de les mateixes diagonals
%noAmenacesDiagonals(N,D):-
    %diagonals(N,L), llistesDiagonalsAVars(L,N,VARS), ...
%més complicat: tens les diagonals generades per diagonals/2, després converteixes coordenades a variables i poses comamoltUn/2 per evitar més d’una reina a la diagonal
noAmenacesDiagonals(N,CNF):-
    diagonals(N,L),
    llistesDiagonalsAVars(L,N,LV),
    filtraDiagonals(LV,LF),
    noAmenacesDiagonals_aux(LF,CNF).

noAmenacesDiagonals_aux([],[]).
noAmenacesDiagonals_aux([D|Ds],Res):-
    comamoltUn(D,CNFd),
    noAmenacesDiagonals_aux(Ds,R),
    append(CNFd,R,Res).

llistesDiagonalsAVars([],_,[]).
llistesDiagonalsAVars([L|Ls],N,[V|Vs]):-
    coordenadesAVars(L,N,V),
    llistesDiagonalsAVars(Ls,N,Vs).


filtraDiagonals([],[]).
filtraDiagonals([D|Ds],[D|R]):-
    length(D,L),
    L > 1, !,
    filtraDiagonals(Ds,R).
filtraDiagonals([_|Ds],R):-
    filtraDiagonals(Ds,R).

%%%%%%%%%%%%%%%%%%%%%
% minimNReines(+V,FN)
% donada la matriu de variables (inicialment d'un tauler NxN),
% -> FN sera la CNF que codifiqui que hi ha dhaver com a minim N reines al tauler
% ...
minimNReines(_,[]).


% AUX
% llista(I,F,L)
% Donat un inici i un fi
% -> el tercer parametre sera una llista de numeros d'inici a fi
% ...
llista(I,F,[]):- I>F, !.
llista(I,F,[I|Xs]):- I=<F, I1 is I +1, llista(I1,F,Xs). 

% trosseja(L,N,LL)
% Donada una llista (L) i el numero de trossos que en volem (N)
% -> LL sera la llista de N llistes de L amb la mateixa mida
% (S'assumeix que la llargada de L i N ho fan possible)
% ...
trosseja(L,N,LL):-
	length(L,Len),
	CutSize is Len // N,
	trosseja_aux(L,CutSize,LL),!.
	
% Genera una llista de N llistes de L amb la mateixa mida
trosseja_aux([],_,[]).
trosseja_aux(L,S,[X|LLs]):-
	append(X,Y,L),
	length(X,S),!,
	trosseja_aux(Y,S,LLs).

% AUX
% fixa(PI,N,F)
% donada una llista de tuples de posicions PI i una mida de tauler N
% -> F es la CNF fixant les corresponents variables de posicions a certa
% ...
fixa([],_,[]).
fixa([(F,C)|PIs],N,[[R]|Rs]):-
	R is (F-1)*N + C,
	R =< N**N,
	fixa(PIs,N,Rs).


% AUX
% prohibeix(PP,N,P)
% donada una llista de tuples de posicions prohibides PP i una mida  tauler N
% -> P es la CNF posant les corresponents variables de posicions a fals
% ...
prohibeix([],_,[]).
prohibeix([(F,C)|PPs],N,[[-R]|Rs]):-
	R is (F-1)*N + C,
	R =< N**N,
	prohibeix(PPs,N,Rs).





%%%%%%%%%%%%
% sat(F,I,M)
% si F es satisfactible, M sera el model de F afegit a la interpretació I (a la primera crida I sera buida).
% Assumim invariant que no hi ha literals repetits a les clausules ni la clausula buida inicialment.

%sat([],I,I):-     write('SAT!!'),nl,!.
%sat(CNF,I,M):-
% Ha de triar un literal d’una clausula unitaria, si no n’hi ha cap, llavors un literal pendent qualsevol.
%decideix(CNF,Lit),

% Simplifica la CNF amb el Lit triat (compte pq pot fallar, es a dir si troba la clausula buida fallara i fara backtraking).
%simplif(Lit,CNF,CNFS).

% crida recursiva amb la CNF i la interpretacio actualitzada
%sat(... , ... ,M).


%%%%%%%%%%%%%%%%%%
% decideix(F, Lit)
% Donat una CNF,
% -> el segon parametre sera un literal de CNF
%  - si hi ha una clausula unitaria sera aquest literal, sino
%  - un qualsevol o el seu negat.
% ...

%%%%%%%%%%%%%%%%%%%%%
% simlipf(Lit, F, FS)
% Donat un literal Lit i una CNF,
% -> el tercer parametre sera la CNF que ens han donat simplificada:
%  - sense les clausules que tenen lit
%  - treient -Lit de les clausules on hi es, si apareix la clausula buida fallara.
% ...

mostraTauler(N,M):-
    mostraFiles(1,N,N,M).

mostraFiles(F,N,_,_):- F > N, !.
mostraFiles(F,N,Size,M):-
    mostraSeparador(Size),
    mostraColumnes(F,1,Size,M),
    F1 is F+1,
    mostraFiles(F1,N,Size,M).

mostraSeparador(0):- nl.
mostraSeparador(N):- 
    write('---'),
    N1 is N-1,
    mostraSeparador(N1).

mostraColumnes(_,C,N,_):- C > N, write('|'), nl, !.
mostraColumnes(F,C,N,M):-
    Pos is (F-1)*N + C,
    write('|'),
    mostraCasella(Pos,M),
    C1 is C+1,
    mostraColumnes(F,C1,N,M).

mostraCasella(Pos,M):-
    member(Pos,M), !,
    write('Q').
mostraCasella(_, _):-
    write(' ').
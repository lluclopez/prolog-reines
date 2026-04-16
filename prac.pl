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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


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
    
comamoltUn_aux(L, [], []).
comamoltUn_aux(L, [Ls|Lss], [[NL, NLs] | R]) :-
    NL is -L,
    NLs is -Ls,
    comamoltUn_aux(L, Lss, R).

%comamoltUn_aux(L,[],[]).
%comamoltUn_aux(L,[Ls|Lss],[[-L,-Ls]|R]):-
%	comamoltUn_aux(L,Lss,R).

%%%%%%%%%%%%%%%%%%%
% exactamentUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que exactament una sigui certa.
% ...
exactamentUn(L,CNF):-
	comaminimUn(L,R1),
	comamoltUn(L,R2),
	append(R1,R2,CNF).

%%%%%%%%%%%%%%%%%%%%%%%%%%%
% fesTauler(+N,+PI,+PP,V,I)
% Donat una dimensio de tauler N, unes posicions inicials PI i
% unes prohibides PP
% -> V sera el la llista de llistes variables necessaries per codificar el tauler
% -> I sera la CNF codificant posicions inicials i prohibides
% ...
fesTauler(N,PI,PP,V,I):-
    llista(1,N*N,Vi),
    trosseja(Vi,N,V),
    fixa(PI,N,R1),
    prohibeix(PP,N,R2),
    append(R1,R2,I).


% AUX
% llista(I,F,L)
% Donat un inici i un fi
% -> el tercer parametre sera una llista de numeros d'inici a fi
% ...
llista(I,F,[]):- I>F, !.
llista(I,F,[I|Xs]):- I=<F, I1 is I +1, llista(I1,F,Xs). 

% AUX
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
trosseja_aux(L,CutSize,[X|LLs]):-
	append(X,Y,L),
	length(X,CutSize),!,
	trosseja_aux(Y,CutSize,LLs).

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
prohibeix([(F,C)|PPs],N,[[NR]|Rs]):-
	R is (F-1)*N + C,
	R =< N**N,
    NR is -R,
	prohibeix(PPs,N,Rs).

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

%%%%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesColumnes(+V,C)
% donada la matriu de variables,
% -> C sera la CNF que codifiqui que no samenecen les reines de les mateixes columnes
% ...
noAmenacesColumnes([], []).        % Seguretat per si entra una matriu buida
noAmenacesColumnes([[] | _], []).
noAmenacesColumnes(V, F):-
    extreuColumna(V, Columna1, RestaMatriu),
    comamoltUn(Columna1, Restant),
    noAmenacesColumnes(RestaMatriu, F_resta),
    append(Restant,F_resta,F).

% 
extreuColumna([], [], []).
extreuColumna([[Primer | RestaColumnes] | RestaFiles], [Primer | RestaColumna], [RestaColumnes | RestaMatriu]) :-
    extreuColumna(RestaFiles, RestaColumna, RestaMatriu).


% AQUEST PREDICAT ESTA PARCIALMENT FET. CAL QUE CALCULEU LES "ALTRES"
% DIAGONALS
%%%%%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesDiagonals(+N,C)
% donada la mida del tauler,
% -> D sera la CNF que codifiqui que no samenecen les reines de les mateixes diagonals
noAmenacesDiagonals(N, D):-
    diagonals(N, L), 
    llistesDiagonalsAVars(L, N, VARS), 
    protegeixDiagonals(VARS, D). 


% Genera les llistes de diagonals d'una matriu NxN. Cada diagonal es una llista de coordenades.
diagonals(N, L):- diagonalsIn(1, N, L1), diagonals2In(1, N, L2), append(L1, L2, L).

% diagonalsIn(D,N,L)
% Generem les diagonals dalt-dreta a baix-esquerra, D es el numero de
% diagonals, N la mida del tauler i L seran les diagonals generades
% Exemple:
% ?- diagonalsIn(1,3,L).
% L = [[(1,1)],[(1,2),(2,1)],[(1,3),(2,2),(3,1)],[(2,3),(3,2)],[(3,3)]]
% Evidentment les diagonals amb una sola coordenada les ignorarem...

diagonalsIn(D, N, []) :- D is 2*N, !.
diagonalsIn(D, N, [L1|L]) :- D =< N, fesDiagonal(1, D, L1), D1 is D+1, diagonalsIn(D1, N, L).
diagonalsIn(D, N, [L1|L]) :- D > N, F is D-N+1, fesDiagonalReves(F, N, N, L1), D1 is D+1, diagonalsIn(D1, N, L).

fesDiagonal(F, 1, [(F,1)]) :- !.
fesDiagonal(F, C, [(F,C)|R]) :- F1 is F+1, C1 is C-1, fesDiagonal(F1, C1, R).

% quan la fila es N parem
fesDiagonalReves(N, C, N, [(N,C)]) :- !.
fesDiagonalReves(F, C, N, [(F,C)|R]) :- F1 is F+1, C1 is C-1, fesDiagonalReves(F1, C1, N, R).


% diagonals2In(D,N,L)
% Generem les diagonals baix-dreta a dalt-esquerra
diagonals2In(D, N, []) :- D is 2*N, !.
diagonals2In(D, N, [L1|L]) :- D =< N, fes2Diagonal(1, D, N, L1), D1 is D+1, diagonals2In(D1, N, L).
diagonals2In(D, N, [L1|L]) :- D > N, F is D-N+1, fesDiagonal2Reves(F, 1, N, L1), D1 is D+1, diagonals2In(D1, N, L).

fes2Diagonal(F, N, N, [(F,N)]) :- !.
fes2Diagonal(F, C, N, [(F,C)|R]) :- F1 is F+1, C1 is C+1, fes2Diagonal(F1, C1, N, R).

% quan la fila es N parem
fesDiagonal2Reves(N, C, N, [(N,C)]) :- !.
fesDiagonal2Reves(F, C, N, [(F,C)|R]) :- F1 is F+1, C1 is C+1, fesDiagonal2Reves(F1, C1, N, R).


% Passa una llista de coordenades de tauler NxN a variables corresponents.
coordenadesAVars([], _, []).
coordenadesAVars([(F,C)|R], N, [V|RV]) :- V is (F-1)*N+C, coordenadesAVars(R, N, RV).


% Passa una llista de diagonals a llistes de llistes de variables
llistesDiagonalsAVars([], _, []).
llistesDiagonalsAVars([Diagonal | RestaDiagonals], N, [VarsDiagonal | RestaVars]):- 
    coordenadesAVars(Diagonal, N, VarsDiagonal),
    llistesDiagonalsAVars(RestaDiagonals, N, RestaVars).

% Aplica comamoltUn a cada diagonal de la llista i ho junta tot a D
protegeixDiagonals([], []). 
protegeixDiagonals([Cap | Cua], D):- 
    comamoltUn(Cap, D_Cap), 
    protegeixDiagonals(Cua, D_cua), 
    append(D_Cap, D_cua, D).

%%%%%%%%%%%%%%%%%%%%%
% minimNReines(+V,FN)
% donada la matriu de variables (inicialment d'un tauler NxN),
% -> FN sera la CNF que codifiqui que hi ha d'haver com a minim N reines al tauler
% ...
minimNReines(X,X).


%%%%%%%%%
% resol()
% Ens demana els parametres del tauler i lestat inicial,
% codifica les restriccions del problema i en fa una formula
% que la enviem a resoldre amb el SAT solver
% i si te solucio en mostrem el tauler
resol:-
    write('Mida del tauler? '), read(N),
    write('Posicions inicials? '), read(I),
    write('Posicions prohibides? '), read(P),

    fesTauler(N,I,P,V,Ini),

    write('Variables tauler: '), write(V), nl,
    write('CNF inicial: '), write(Ini), nl,

    minimNReines(V,FN),
    noAmenacesFiles(V,CNFfiles),
    noAmenacesColumnes(V,CNFcolumnes),
	%CNFcolumnes = [],
    noAmenacesDiagonals(N,CNFdiagonals),
	%CNFdiagonals = [],

    append(Ini,FN,T1),
    append(T1,CNFfiles,T2),
    append(T2,CNFcolumnes,T3),
    append(T3,CNFdiagonals,CNF),

    write('CNF total: '), write(CNF), nl,

    sat(CNF,[],M),

    write('Model: '), write(M), nl,

    literalsPositius(M,Pos),
    mostraTauler(N,Pos),
    nl,
    fail. % Una vegada ha trobat una solució, fail per a què faci backtracking i en trobi una altra.

literalsPositius([],[]).
literalsPositius([X|Xs],[X|R]):- X > 0, !, literalsPositius(Xs,R).
literalsPositius([_|Xs],R):- literalsPositius(Xs,R).


%%%%%%%%%%%%%%%%%%%
% mostraTauler(N,M)
% donat una mida de tauler N i una llista de numeros d'1 a N*N,
% mostra el tauler posant una Q a cada posicio recorrent per files
% d'equerra a dreta.
% Per exemple:
% | ?- mostraTauler(3,[1,5,8,9...]).
% -------
% |Q| | |
% -------
% | |Q| |
% -------
% | |Q|Q|
% -------
% Fixeu-vos que li passarem els literals positius del model de la nostra
% formula.
% ...
mostraTauler(N,M):-
    mostraFiles(1,N,N,M).

% Cas base: si la fila actual (F) supera la mida del tauler (N), vol dir que hem acabat de dibuixar.
mostraFiles(F,N,_,_):- F > N, !.
mostraFiles(F,N,Size,M):- % Per a cada fila, dibuixem primer la línia separadora superior,
    mostraSeparador(Size), % després omplim les columnes d'esquerra a dreta, i finalment fem la crida recursiva incrementant l'índex de la fila.
    mostraColumnes(F,1,Size,M),
    F1 is F+1,
    mostraFiles(F1,N,Size,M).

% Cas base: quan hem dibuixat els N blocs, fem un salt de línia.
mostraSeparador(0):- nl. % Es podria posar un ! aqui tambe en comptes de N>0.
mostraSeparador(N):- % Dibuixa un tram de la línia separadora i crida recursivament.
    N > 0, % Sense aquesta restricció, el predicat entraria en un bucle infinit perquè N unifica amb infinits valors negatius.
    write('---'),
    N1 is N-1,
    mostraSeparador(N1).

% Cas base: si la columna actual supera l'amplada,tanquem la casella amb el pal vertical dret i fem un salt de línia.
mostraColumnes(_,C,N,_):- C > N, write('|'), nl, !.
mostraColumnes(F,C,N,M):-
    Pos is (F-1)*N + C, % convertim les coordenades de matriu 2D (Fila, Columna) al seu índex Pos.
    write('|'),
    mostraCasella(Pos,M),
    C1 is C+1,
    mostraColumnes(F,C1,N,M).

mostraCasella(Pos,M):- % Comprova si a la posició actual hi va una reina.
    member(Pos,M), !,
    write('Q').
mostraCasella(_, _):-
    write(' ').
%%%%%%%%%%%%
% sat(F,I,M)
% si F es satisfactible, M sera el model de F afegit a la interpretació I (a la primera crida I sera buida).
% Assumim invariant que no hi ha literals repetits a les clausules ni la clausula buida inicialment.

% Cas base: si la CNF és buida, vol dir que hem satisfet totes les clàusules, per tant, la interpretació és un model.
sat([],I,I):- write('SAT!!'),nl,!.
sat(CNF,I,M):-
% Ha de triar un literal d’una clausula unitaria, si no n’hi ha cap, llavors un literal pendent qualsevol.
decideix(CNF,Lit),

% Simplifica la CNF amb el Lit triat (compte pq pot fallar, es a dir si troba la clausula buida fallara i fara backtraking).
simplif(Lit,CNF,CNFS),

% crida recursiva amb la CNF i la interpretacio actualitzada
sat(CNFS,[Lit|I],M).

%%%%%%%%%%%%%%%%%%
% decideix(F, Lit)
% Donat una CNF,
% -> el segon parametre sera un literal de CNF
%  - si hi ha una clausula unitaria sera aquest literal, sino
%  - un qualsevol o el seu negat.
% ...
decideix(CNF, Lit) :- % Clausula unitària
    member([Lit], CNF), !.
decideix([[L|_] | _], L). % primer literal
decideix([[L|_] | _], Lit) :- % primer literal negat
    Lit is -L.

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

% elimina(X,L,R) treu totes les aparicions de X a la llista L i el resultat el posa a R
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
    
% comamoltUn_aux(L,Ls,R) donada una variable i una llista de variables,
% genera la CNF que codifica que no poden ser certes al mateix temps
comamoltUn_aux(L, [], []).
comamoltUn_aux(L, [Ls|Lss], [[NL, NLs] | R]) :-
    NL is -L,
    NLs is -Ls,
    comamoltUn_aux(L, Lss, R).

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

% trosseja_aux(L,CutSize,LL)
% Donada una llista L i una mida de trossos CutSize
% -> LL sera la llista de trossos de L que tenen mida CutSize
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
% -> F sera la CNF que codifiqui que no s'amenecen les reines de les mateixes files
% ...
noAmenacesFiles([],[]).
noAmenacesFiles([L|Ls],R):-
	exactamentUn(L,CNF),
	noAmenacesFiles(Ls,F),
	append(CNF,F,R).

%%%%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesColumnes(+V,C)
% donada la matriu de variables,
% -> C sera la CNF que codifiqui que no s'amenecen les reines de les mateixes columnes
% ...
noAmenacesColumnes([], []).        % No cal, és seguretat per si entra una matriu buida
noAmenacesColumnes([[] | _], []).
noAmenacesColumnes(V, F):-
    extreuColumna(V, Columna1, RestaMatriu),
    comamoltUn(Columna1, Restant),
    noAmenacesColumnes(RestaMatriu, F_resta),
    append(Restant,F_resta,F).

% extreuColumna(Matriu, Columna, RestaMatriu)
% Donada una matriu, extreu la primera columna i deixa la resta de la matriu
extreuColumna([], [], []).
extreuColumna([[Primer | RestaColumnes] | RestaFiles], [Primer | RestaColumna], [RestaColumnes | RestaMatriu]) :-
    extreuColumna(RestaFiles, RestaColumna, RestaMatriu).

% AQUEST PREDICAT ESTA PARCIALMENT FET. CAL QUE CALCULEU LES "ALTRES"
% DIAGONALS
%%%%%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesDiagonals(+N,C)
% donada la mida del tauler,
% -> D sera la CNF que codifiqui que no s'amenecen les reines de les mateixes diagonals
noAmenacesDiagonals(N, D):-
    diagonals(N, L),  % Obtenim les llistes de coordenades 2D de totes les diagonals del tauler.
    llistesDiagonalsAVars(L, N, VARS), % Traduïm coordenades als identificadors corresponents.
    protegeixDiagonals(VARS, D). % Apliquem "com a molt una" a cada diagonal.


% Genera les llistes de diagonals d'una matriu NxN. Cada diagonal es una llista de coordenades.
diagonals(N,L):- diagonalsIn(1,N,L1), diagonals2In(1,N,L2), append(L1,L2,L).

% diagonalsIn(D,N,L)
% Generem les diagonals dalt-dreta a baix-esquerra, D es el numero de
% diagonals, N la mida del tauler i L seran les diagonals generades
% Exemple:
% ?- diagonalsIn(1,3,L).
% L = [[(1,1)],[(1,2),(2,1)],[(1,3),(2,2),(3,1)],[(2,3),(3,2)],[(3,3)]]
% Evidentment les diagonals amb una sola coordenada les ignorarem...

diagonalsIn(D,N,[]):-D is 2*N,!.
diagonalsIn(D,N,[L1|L]):- D=<N,fesDiagonal(1,D,L1), D1 is D+1, diagonalsIn(D1,N,L).
diagonalsIn(D,N,[L1|L]):- D>N, F is D-N+1,fesDiagonalReves(F,N,N,L1), D1 is D+1, diagonalsIn(D1,N,L).

fesDiagonal(F,1,[(F,1)]):- !.
fesDiagonal(F,C,[(F,C)|R]):- F1 is F+1, C1 is C-1, fesDiagonal(F1,C1,R).

% quan la fila es N parem
fesDiagonalReves(N,C,N,[(N,C)]):-!.
fesDiagonalReves(F,C,N,[(F,C)|R]):-F1 is F+1, C1 is C-1, fesDiagonalReves(F1,C1,N,R).



% diagonals2In(D,N,L)
% Generem les diagonals baix-dreta a dalt-esquerra
% Exemple
% ?- diagonals2In(1,3,L).
% L = [[(3,1)],[(3,2),(2,1)],[(3,3),(2,2),(1,1)],[(2,3),(1,2)],[(1,3)]]
% ...
diagonals2In(D, N, []) :- D is 2*N, !.
diagonals2In(D, N, [L1|L]) :- D =< N, fes2Diagonal(1, D, N, L1), D1 is D+1, diagonals2In(D1, N, L).                     % Començem sempre a la fila 1 i avancem la columna d'inici D (meitat superior del tauler)
diagonals2In(D, N, [L1|L]) :- D > N, F is D-N+1, fesDiagonal2Reves(F, 1, N, L1), D1 is D+1, diagonals2In(D1, N, L).     % Processa la meitat inferior del tauler (quan D > N). La columna d'inici passa a ser sempre la 1, però la fila d'inici va baixant (D-N+1).

% fes2Diagonal(F,C,N,L)
% Genera una diagonal baix-dreta a dalt-esquerra, F es la fila d'inici, C la columna d'inici, N la mida del tauler i L la
fes2Diagonal(F, N, N, [(F,N)]) :- !.
fes2Diagonal(F, C, N, [(F,C)|R]) :- F1 is F+1, C1 is C+1, fes2Diagonal(F1, C1, N, R).

% fesDiagonal2Reves(F,C,N,L)
% Genera una diagonal dalt-esquerra a baix-dreta, F es la fila d'inici, C la columna d'inici, N la mida del tauler i L la
fesDiagonal2Reves(N, C, N, [(N,C)]) :- !.
fesDiagonal2Reves(F, C, N, [(F,C)|R]) :- F1 is F+1, C1 is C+1, fesDiagonal2Reves(F1, C1, N, R).

% Passa una llista de coordenades  de tauler NxN a variables corresponents.
coordenadesAVars([],_,[]).
coordenadesAVars([(F,C)|R],N,[V|RV]):-V is (F-1)*N+C, coordenadesAVars(R,N,RV).

% Passa una llista de diagonals a llistes de llistes de variables
%llistesDiagonalsAVars(Lparells,N,Lvars).
%...
% Converteix una llista de diagonals (coordenades 2D) en llistes de variables (índexs 1D).
llistesDiagonalsAVars([], _, []).
llistesDiagonalsAVars([Diagonal | RestaDiagonals], N, [VarsDiagonal | RestaVars]):- 
    coordenadesAVars(Diagonal, N, VarsDiagonal),
    llistesDiagonalsAVars(RestaDiagonals, N, RestaVars).

% Genera la CNF per garantir que hi hagi, com a molt, una reina per diagonal.
% Cas base: Sense diagonals, la llista de clàusules resultant és buida.
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
minimNReines(X,X). % La matriu de variables ja és una CNF que codifica que hi ha d'haver com a minim N reines al tauler, ja que cada variable representa una possible reina.


%%%%%%%%%
% resol()
% Ens demana els parametres del tauler i l'estat inicial,
% codifica les restriccions del problema i en fa una formula
% que la enviem a resoldre amb el SAT solver
% i si te solucio en mostrem el tauler
resol:-
    write('Mida del tauler? '), read(N),
    write('Posicions inicials? '), read(I),
    write('Posicions prohibides? '), read(P),

    fesTauler(N,I,P,V,Ini), % generem V i Ini

    write('Variables tauler: '), write(V), nl,
    write('CNF inicial: '), write(Ini), nl,

    minimNReines(V,FN),
    noAmenacesFiles(V,CNFfiles),
    noAmenacesColumnes(V,CNFcolumnes),
    noAmenacesDiagonals(N,CNFdiagonals),

    append(Ini,FN,T1),
    append(T1,CNFfiles,T2),
    append(T2,CNFcolumnes,T3),
    append(T3,CNFdiagonals,CNF), % unim les CNF parcials per obtenir la CNF final

    write('CNF final: '), write(CNF), nl,

    sat(CNF,[],M), % resolem la CNF, M serà el model que satisfà la CNF, és a dir, la llista de literals que ens indica si hi ha o no reina a cada posició del tauler.

    write('Model: '), write(M), nl,

    literalsPositius(M,Pos),
    mostraTauler(N,Pos),
    nl,
    fail.

% literalsPositius(L,Pos)
% Donada una llista de literals (L), retorna una llista amb els literals positius (Pos).
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
mostraFiles(F,N,Size,M):-       % Per a cada fila, dibuixem primer la línia separadora superior,
    mostraSeparador(Size),      % després omplim les columnes d'esquerra a dreta, i finalment fem la crida recursiva incrementant l'índex de la fila.
    mostraColumnes(F,1,Size,M), 
    F1 is F+1,
    mostraFiles(F1,N,Size,M).   


% Cas base: quan hem dibuixat els N blocs, fem un salt de línia.
mostraSeparador(0):- nl.        % Es podria posar un ! aqui tambe en comptes de N>0.
mostraSeparador(N):-            % Dibuixa un tram de la línia separadora i crida recursivament.
    N > 0,                      % És vital aquí aquesta línia o (el ! a dalt), evita que si el programa fa backtracking 
    write('---'),               % Prolog intenti dibuixar separadors de longitud negativa, el que provocaria un bucle infinit.
    N1 is N-1,                  
    mostraSeparador(N1).


% Cas base: si la columna actual supera l'amplada,tanquem la casella amb el pal vertical dret i fem un salt de línia.
mostraColumnes(_,C,N,_):- C > N, write('|'), nl, !.
mostraColumnes(F,C,N,M):-       % Pas recursiu de les columnes: per saber quina variable del SAT solver estem avaluant,
    Pos is (F-1)*N + C,         % convertim les coordenades de matriu 2D (Fila, Columna) al seu índex Pos.
    write('|'),
    mostraCasella(Pos,M),
    C1 is C+1,
    mostraColumnes(F,C1,N,M).

mostraCasella(Pos,M):-          % Comprova si a la posició actual hi va una reina.
    member(Pos,M), !,           % El tall aquí és imprescindible ja que un cop sabem que hi ha una reina
    write('Q').                 % no volem que Prolog, per backtracking, provi d'executar la regla de sota i la deixi buida.
mostraCasella(_, _):-           
    write(' ').







%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%
%%%%%% Joc de proves
%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% prova noAmenacesFiles amb tauler 4x4
% comprovem que hi ha restriccions per cada fila
test_noAmenacesFiles4x4 :-
    V = [[1,2,3,4],[5,6,7,8],[9,10,11,12],[13,14,15,16]],
    noAmenacesFiles(V,F),
    print(F),
    length(F,L),
    L > 0.

% prova noAmenacesColumnes amb tauler 4x4
% comprovem que hi ha restriccions entre elements de columna
test_noAmenacesColumnes4x4 :-
    V = [[1,2,3,4],[5,6,7,8],[9,10,11,12],[13,14,15,16]],
    noAmenacesColumnes(V,CNF),
    print(CNF),
    member([-2,-6],CNF).


% prova noAmenacesDiagonals amb tauler 4x4
% comprovem que hi ha restriccions com (6 i 11), suposem que si aquesta existeix, la resta també.
test_noAmenacesDiagonals4x4 :-
    noAmenacesDiagonals(4,D),
    print(D),
    member([-6,-11],D).


% CNF satisfactible simple
test_satSolver_sat :-
    CNF = [[1,2],[-1,3]],
    sat(CNF,[],M),
    print(M),
    member(3,M).

% CNF insatisfactible
test_satSolver_unsat :-
    CNF = [[1],[-1]],
    \+ sat(CNF,[],_).

% prova mostraTauler amb tauler 4x4
% configuració vàlida de 4 reines
test_mostraTauler4x4 :-
    M = [2,7,9,16],
    mostraTauler(4,M).

test_fesTauler4x4 :-
    N = 4,
    I = [(1,1)],
    P = [(2,2),(3,3)],
    fesTauler(N,I,P,V,Ini),
    print(V),nl,
    print(Ini).

% test resol amb tauler 4x4 sense restriccions
% hauria de trobar una solució vàlida
test_resol4x4 :-
    N = 4,
    I = [],
    P = [],
    fesTauler(N,I,P,V,Ini),
    noAmenacesFiles(V,F1),
    noAmenacesColumnes(V,F2),
    noAmenacesDiagonals(N,F3),
    append(Ini,F1,R1),
    append(R1,F2,R2),
    append(R2,F3,Total),
    sat(Total,[],M),
    print(M),nl,
    literalsPositius(M,Pos),
    mostraTauler(N,Pos).

% test resol amb posicions inicials
% fixa una reina a (1,1), resposta esperada ha de ser no.
test_resol_inicials :-
    N = 4,
    I = [(1,1)],
    P = [],
    fesTauler(N,I,P,V,Ini),
    noAmenacesFiles(V,F1),
    noAmenacesColumnes(V,F2),
    noAmenacesDiagonals(N,F3),
    append(Ini,F1,R1),
    append(R1,F2,R2),
    append(R2,F3,Total),
    sat(Total,[],M),
    print(M),
    member(1,M).
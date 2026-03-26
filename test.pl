
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

sat([],I,I):-     write('SAT!!'),nl,!.
sat(CNF,I,M):-
% Ha de triar un literal d’una clausula unitaria, si no n’hi ha cap, llavors un literal pendent qualsevol.
decideix(CNF,Lit),

% Simplifica la CNF amb el Lit triat (compte pq pot fallar, es a dir si troba la clausula buida fallara i fara backtraking).
simplif(Lit,CNF,CNFS),

% crida recursiva amb la CNF i la interpretacio actualitzada
sat(... , ... ,M).


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
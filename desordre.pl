%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                   Pràctica Prolog                         %
%   Paradigmes i Llenguatges de Programació, curs 2025      %
%               Gerard Alsina i Lluc López                  %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constant_m_rand(65537).
constant_a_rand(75).
constant_c_rand(74).

%treure_nessim(?L,+N,?X,?L2) ==> L2 es la llista L despres d'eliminar el N-essim element, que es X
treure_nessim([X|L],0,X,L):-!.
treure_nessim([X|L],N,Y,[X|L2]):- Nm1 is N-1, treure_nessim(L,Nm1,Y,L2).

%llista_enumerada(+Mida,?L) ==> L = [0,1,2,...,Mida-1]
llista_enumerada(Mida,L):- Nm1 is Mida-1, findall(X,between(0,Nm1,X),L).

%llista_aleatoria(+N,+Llavor,-L)
% L es una permutacio aleatoria de la llista [1,2,...,N], construida a partir de la llavor Llavor
llista_aleatoria(Mida,Llavor,Llista):-
    llista_enumerada(Mida,LlistaOrdenada),
    llista_aleatoria_(Mida,LlistaOrdenada,Llista,Llavor).

%Auxiliar per llista_aleatoria, NO UTILITZAR
llista_aleatoria_(0,[],[],_):-!.
llista_aleatoria_(N,Llista,[X|RestaPermutats],Llavor):-
    Pos is Llavor mod N,
    treure_nessim(Llista,Pos,X,LlistaPermutada),
    constant_m_rand(M),
    constant_a_rand(A),
    constant_c_rand(C),
    RandNext is (A * Llavor + C) mod M,
    Nm1 is N-1,
    llista_aleatoria_(Nm1,LlistaPermutada,RestaPermutats,RandNext).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% mostrar_llista(+L)
mostrar_llista([X|[Y|Z]]):-
    print(X),
    print(','),
    mostrar_llista([Y|Z]),
    !.
mostrar_llista([Ultim]):-
    print(Ultim),nl,
    !.

% contar_des(+Llista, +posicio, +Comptador, -N.Desubicats)
contar_des(L, Res) :-
    length(L, N), % Obtenim la llargada de la llista
    findall(Pos, (
        between(0, N, Pos), % Generem índexs de 0 a N
        append(Esquerra, [X|_], L), % Dividim la llista en dues parts
        %[],[0|6,3,4]
        %[0],[6|3,4]
        %[0,6],[3|4]
        %[0,6,3],[4]
        length(Esquerra, Pos), % Ens assegurem que l'element X està a la posició correcta
        X \= Pos % Comprovem si està desubicat
    ), Desubicats),
    length(Desubicats, Res). % Comptem quants elements estan desubicats

% EXERCICI 1
% nombre_desubicats(+L,?Des)
nombre_desubicats(L,Des) :- ordena(L,Res), compara(L,Res,Des).

ordena([],[]).
ordena([X|Xs], Ord):-ordena(Xs,OrdCua), insereix(X, OrdCua, Ord).

insereix(X, [], [X]).
insereix(X, [Y|Ys], [X,Y|Ys]) :- X =< Y.
insereix(X, [Y|Ys], [Y|R]) :- X > Y, insereix(X, Ys, R).

compara([],[],0).
compara([X|Xs], [Y|Ys], Des) :- X==Y, compara(Xs,Ys,Des).
compara([X|Xs], [Y|Ys], Des) :- X\==Y, compara(Xs, Ys, Des1), Des is Des1+1.


% EXERCICI 2
suma_desplacaments(L,Sum):-ordena(L,Res), conta_desp(L,Res,Sum).

conta_desp([],[],0).
conta_desp([X|Xs], [X|Ys], Sum) :- conta_desp(Xs,Ys,Sum).
conta_desp([X|Xs], [Y|Ys], Sum) :- X\=Y, conta_desp([X|Xs], Ys, Sum1), Sum is Sum1+1.

conta_desp([], [], 0).
conta_desp([X|Xs], [Y|Ys], Sum):- 
    buscar_pos(X, [Y|Ys], Pos),
    buscar_pos(Y, [Y|Ys], PosY),
    Desp is abs(Pos - PosY),
    conta_desp(Xs, [Y|Ys], Sum1),
    Sum is Sum1+Desp.

buscar_pos(Elem, [Elem|_], 0).
buscar_pos(Elem, [_|Rest], Pos):- 
    buscar_pos(Elem, Rest, PosRest), 
    Pos is PosRest + 1.

%Exercici 3
% a_inserir(+L, ?L2, ?Pas)
% L2 es el resultat d'aplicar l'acció inserir a L, y Pas conté la tupla
% pas_inserir(Prefix1, Prefix2, Fragment, Sufix)

a_inserir(L, L2, Pas) :-
    % Dividir la llista L en Prefix, Prefix2 y Sufix
    append(Prefix1, [PrimerPrefix2 | RestoPrefix2], Prefix),
    append([PrimerPrefix2 | RestoPrefix2], Fragment, LMitat),
    append(LMitat, Sufix, L),

    % Prefix2 no pot estar buit
    Prefix2 = [PrimerPrefix2 | RestoPrefix2],

    % Verificar que Prefix y Fragment estan ordenats
    ordenada(Prefix),
    ordenada(Fragment),

    % Verificar la condició d'ordre entre Prefix1 y Fragment
    verificar_ultima_condicio(Prefix1, Fragment),

    % Condició d'ordre entre l'últim de Fragment y el primer de Prefix2
    Fragment = [_ | _],
    ultimo(Fragment, UltimFragment),
    UltimFragment < PrimerPrefix2,

    % Crear L2 inserint Fragment entre Prefix1 y Prefix2
    append(Prefix1, Fragment, Part1),
    append(Part1, Prefix2, Part2),
    append(Part2, Sufix, L2),

    % Crear la tupla de pas
    Pas = pas_inserir(Prefix1, Prefix2, Fragment, Sufix).

% Verificar si la última condició ex compleix per Prefix1
verificar_ultima_condicio([], _).
verificar_ultima_condicio(Prefix1, [PrimerFragment | _]) :-
    ultim(Prefix1, UltimPrefix1),
    UltimPrefix1 < PrimerFragment.

% Verifica si una lista está ordenada de forma creciente
ordenada([]).
ordenada([_]).
ordenada([X, Y | Resto]) :-
    X =< Y,
    ordenada([Y | Resto]).

% Encuentra el último elemento de una lista
ultim([X], X).
ultim([_ | L], X) :-
    ultim(L, X).


% EXERCICI 4
%a capgirar(+L,?L2,Pas)
a_capgirar(L, L2, Pas):- Pas=pas_capgirar(Pref,Frag,Suf).

% Capgirar tot:
pas_capgirar([],Frag,[]):- capgira(Frag,Frag).
capgira([],[]).
capgira([X|L1],L2):-capgira(L1,L3),afegeixFinal(X,L3,L2).
afegeixFinal(X,[],[X]).
afegeixFinal(X,[Y|L1],[Y|L2]):-afegeixFinal(X,L1,L2).

menu(esc, Llista):-
    mostrar_llista(Llista),
    !.
menu(des, Llista):-
    contar_des(Llista, Res),
    print(Res),nl,
    !.
menu(sum, Llista):-
    suma_desplacaments(L,Sum),
    print('Suma de desplacaments: '),
    print(Sum),nl,
    !.
menu(pas, Llista):-print('pas\n'),print(Llista),!.
menu(pase, Llista):-print('pase\n'),print(Llista),!.
menu(sor, _):-!.
menu(_,_):-print('Opcio incorrecte\n').

% llegir_llista(+Mode,-Llista)
llegir_llista(m, Llista):-
    print('Entra la llista:\n'),
    read(Llista),
    !.
llegir_llista(a, Llista):-
    print('Entra la mida de la llista:\n'),
    read(Mida),
    print('Entra la llavor:\n'),
    read(Llavor),
    llista_aleatoria(Mida,Llavor,Llista),
    !.

main:-
    print('Llista manual (m) o aleatoria (a) ?'),
    read(Manual),
    llegir_llista(Manual, Llista),
    repeat,
    print('Entrar opcio:'),nl,
    print('- Escriure llista: esc'),nl,
    print('- Calcular desordre amb nombre de desubicats: des'),nl,
    print('- Calcular desordre amb suma de desplacaments: sum'),nl,
    print('- Calcular desordre amb nombre minim de passos: pas'),nl,
    print('- Calcular desordre amb nombre minim de passos i escriure passos: pase'),nl,
    print('- Sortir: sor'),nl,
    read(Opcio),
    menu(Opcio, Llista),
    Opcio=sor,
    !.

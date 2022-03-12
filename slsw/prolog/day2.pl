append([], T, T).
append([Head | Tail], T, [Head | R]) :- append(Tail, T, R).

revers([], []).
revers([Head | Tail], R) :- revers(Tail, RevT), append(RevT, [Head], R).

smol([Head], Head).
smol([Head | Tail], R) :- smol(Tail, R1), Head < R1, R = Head.
smol([Head | Tail], R) :- smol(Tail, R1), Head > R1, R = R1.
    
sumMatrix := method(ls, 
    res := 0
    for(i, 0, (ls size) - 1, 
        res = res + (ls at(i) sum)))

sumMatrix(list(list(1,2),list(3,4))) println
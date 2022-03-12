List myAvarage := method(ls, 
    res := 0 
    for(i, 0, self size - 1, 
        res = res + self at(i))
    res / self size)

list(1,2,3) myAvarage println
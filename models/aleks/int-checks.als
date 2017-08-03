assert check1 
{
    all i: Int | 
      (i > 0 => plus[i, i] > i) and 
      (i < 0 => plus[i, i] < i)
}

check check1 for 3 Int

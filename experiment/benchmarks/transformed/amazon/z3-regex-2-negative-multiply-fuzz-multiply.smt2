(declare-const S String)
(assert (str.in.re S (re.++ (str.to.re "ii]]``TTeeEEkkuuBB0055__;;11gg""""bbttppUU<<ssnn77vv11'''\x0b''\x0b'''aabbbbbbwwrr''aakkCCuuXXuubbbb") re.allchar)))
(assert (not (str.in.re S (re.union (re.union (re.union (str.to.re "aaaaaa'''\r''\r'''55GGaa") re.allchar) (str.to.re "cc::00qqtt66nn&&$$==zz;;4499''VVbbbbbb")) re.allchar))))
(check-sat)
(get-model)

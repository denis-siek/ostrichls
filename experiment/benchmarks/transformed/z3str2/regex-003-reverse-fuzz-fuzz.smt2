(declare-const x String)
(assert (= x "y>bTxQ4eS6zp(i'\x0c'Sg_\\8['R*@'\n''\x0c'Fk*""8\\mD+'\x0c'Wt\\U;$=z\\.25C~'\r',_$^76~qS'\x0b'I9,ggu=\\' '2k70-I}YqZ'\r';ZYW.sY7VrMSW'\x0c'\\>,h'\x0b'FGeP{gp7].G@M6Nu,2](=6P"))
(assert (str.in.re x (re.+ (re.union (str.to.re "0%") (str.to.re "/")))))
(check-sat)
(get-model)

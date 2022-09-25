(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.to.int Username) 174))
(assert (> (str.len Username) 0))
(assert (<= (str.len Domainname) 12))
(assert (> (str.len Domainname) 0))
(assert (= Email (str.++ Username (str.++ "@4+`@" Domainname))))
(assert (str.in.re Email (re.union (re.* (re.++ (re.range "a" "z") (re.++ (re.range "A" "Z") (re.range "0" "9")))) (re.++ (str.to.re "@@@") (re.union (re.* (re.union (re.* (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (str.to.re "."))) (re.* (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))))))))
(assert (str.in.re Domainname (re.union (re.++ (re.union (str.to.re "*;N_]g!$2l(|j|") (re.range "0" "5")) (re.++ (re.union (str.to.re "622Jyj") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "00") (str.to.re "^dTCZf"))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re ".") (re.union (re.union (re.++ (str.to.re "nR$n2)'\t'#7") (re.range "0" "5")) (re.++ (re.++ (str.to.re "2;p[2") (re.union (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "lc0;dT'\n'0") (str.to.re "(xg=uFrW"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "q$.") (re.++ (re.++ (re.++ (str.to.re "2j'\x0c'lbpB'\t't255'\t'-.&' 'Fn") (re.range "0" "5")) (re.union (re.union (str.to.re "O22") (re.union (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.++ (str.to.re "0w}' '0_tggO") (str.to.re "11"))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.union (str.to.re ".m+BR.") (re.union (re.++ (str.to.re "2`2\\40#.p^n5") (re.range "0" "5")) (re.++ (re.union (str.to.re "2]'\t'K,shR") (re.union (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.++ (str.to.re "00c?,0") (str.to.re "'\t'U5;1"))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9"))))))))))))))
(check-sat)

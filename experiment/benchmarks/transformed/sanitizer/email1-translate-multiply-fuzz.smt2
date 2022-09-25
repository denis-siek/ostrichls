(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 24))
(assert (> (str.len Username) 0))
(assert (<= (str.len Domainname) 909))
(assert (> (str.to.int Domainname) 0))
(assert (= Email (str.++ Username (str.++ "Z" Domainname))))
(assert (str.in.re Email (re.union (re.+ (re.++ (re.range "a" "z") (re.++ (re.range "A" "Z") (re.range "0" "9")))) (re.union (str.to.re "=") (re.union (re.+ (re.union (re.* (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (str.to.re "K<"))) (re.+ (re.union (re.range "a" "z") (re.++ (re.range "A" "Z") (re.range "0" "9")))))))))
(assert (str.in.re Domainname (re.++ (re.++ (re.union (str.to.re "2'\n'5") (re.range "0" "5")) (re.union (re.union (str.to.re ":") (re.union (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.++ (str.to.re "0") (str.to.re "54k"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.union (str.to.re "<<") (re.++ (re.union (re.union (str.to.re "2y_e+5") (re.range "0" "5")) (re.union (re.++ (str.to.re "'\x0b'ih") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.++ (str.to.re "00") (str.to.re ""))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "w<") (re.union (re.union (re.union (str.to.re "C4ZN&") (re.range "0" "5")) (re.++ (re.union (str.to.re "2") (re.union (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.++ (str.to.re "K:") (str.to.re ""))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "&nJq") (re.++ (re.union (str.to.re "251""s") (re.range "0" "5")) (re.union (re.union (str.to.re "22") (re.union (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "' '") (str.to.re "1W"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9"))))))))))))))
(check-sat)

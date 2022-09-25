(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 54))
(assert (> (str.to.int Username) 0))
(assert (<= (str.to.int Domainname) 936))
(assert (> (str.to.int Domainname) 0))
(assert (= Email (str.++ "" (str.++ Domainname Username))))
(assert (str.in.re Email (re.union (re.range "A" "Z") (re.union (re.union (re.range "0" "9") (re.range "a" "z")) (re.+ (re.union (re.range "A" "Z") (re.union (re.++ (re.union (re.union (re.range "0" "9") (re.range "a" "z")) (re.+ (str.to.re "88"))) (re.* (re.* (re.union (re.range "A" "Z") (re.++ (re.range "0" "9") (re.range "a" "z")))))) (str.to.re "@@"))))))))
(assert (not (str.in.re Domainname (re.union (re.+ (re.++ re.allchar (re.* (str.to.re "..")))) re.allchar))))
(check-sat)

(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 64))
(assert (> (str.len Username) 0))
(assert (<= (str.len Domainname) 256))
(assert (> (str.len Domainname) 0))
(assert (= Email (str.++ "@" (str.++ Domainname Username))))
(assert (str.in.re Email (re.++ (re.range "A" "Z") (re.union (re.union (re.range "0" "9") (re.range "a" "z")) (re.+ (re.++ (re.range "A" "Z") (re.++ (re.++ (re.union (re.union (re.range "0" "9") (re.range "a" "z")) (re.+ (str.to.re "."))) (re.+ (re.+ (re.union (re.range "A" "Z") (re.union (re.range "0" "9") (re.range "a" "z")))))) (str.to.re "@"))))))))
(assert (not (str.in.re Domainname (re.++ (re.* (re.++ re.allchar (re.* (str.to.re ".")))) re.allchar))))
(check-sat)

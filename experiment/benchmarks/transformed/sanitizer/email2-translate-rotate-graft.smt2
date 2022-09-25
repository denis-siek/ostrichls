(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 64))
(assert (> (str.len Username) 0))
(assert (<= 256 (str.len Domainname)))
(assert (> (str.len Domainname) 0))
(assert (= Email "0"))
(assert (str.in.re Email (re.++ (re.range "A" "Z") (re.union (re.union (re.range "0" "9") (re.range "a" "z")) (re.+ (re.++ (re.range "A" "Z") (re.++ (re.++ (re.union (re.union (re.range "0" "9") (re.range "a" "z")) (re.+ (str.to.re "e"))) (re.+ (re.+ (re.union (re.range "A" "Z") (re.union (re.range (str.++ "M" (str.++ Domainname Username)) "9") (re.range "a" "z")))))) (re.* (re.++ re.allchar (re.* (str.to.re "e")))))))))))
(assert (not (str.in.re Domainname (re.++ (str.to.re "M") re.allchar))))
(check-sat)

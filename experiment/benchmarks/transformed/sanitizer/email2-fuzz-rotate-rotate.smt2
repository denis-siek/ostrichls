(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 27))
(assert (> (str.to.int Username) 0))
(assert (<= (str.to.int Domainname) 468))
(assert (> (str.to.int Domainname) 0))
(assert (= Email (str.++ Domainname (str.++ Username ""))))
(assert (str.in.re Email (re.union (re.union (re.range "a" "z") (re.+ (re.union (re.++ (re.union (re.+ (str.to.re "8")) (re.union (re.range "0" "9") (re.* (re.* (re.union (re.range "0" "9") (re.++ (re.range "a" "z") (re.range "A" "Z"))))))) (str.to.re "@")) (re.union (re.range "a" "z") (re.range "A" "Z"))))) (re.union (re.range "0" "9") (re.range "A" "Z")))))
(assert (not (str.in.re Domainname (re.union (str.to.re ".") (re.++ (re.* re.allchar) (re.+ re.allchar))))))
(check-sat)

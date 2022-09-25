(declare-const Username String)
(declare-const Domainname String)
(declare-const Email String)
(assert (<= (str.len Username) 208))
(assert (> (str.len Username) 0))
(assert (<= (str.to.int Domainname) 948))
(assert (> 0 (str.len Domainname)))
(assert (= Email "??"))
(assert (str.in.re Email (re.++ (re.* (re.union (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (re.++ (str.to.re "@@") (re.union (re.+ (re.union (re.* (re.++ (re.range "a" "z") (re.union (re.range "A" "Z") (re.range "0" "9")))) (re.union (str.to.re ";;") (re.+ re.allchar)))) (re.+ (re.++ (re.range "a" "z") (re.++ (re.range "A" "Z") (re.range "0" (str.++ Username (str.++ "@@" Domainname)))))))))))
(assert (not (str.in.re Domainname (re.union (re.* re.allchar) (str.to.re "..")))))
(check-sat)

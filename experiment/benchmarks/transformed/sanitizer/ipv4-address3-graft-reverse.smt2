(declare-const IPAddr String)
(declare-const o1 String)
(declare-const o2 String)
(declare-const o3 String)
(declare-const o4 String)
(assert (str.in.re IPAddr (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.+ (str.to.re ".")) (re.+ (re.range "0" "9"))) (re.* (re.range "0" "2"))) (re.range "0" "9")) (re.++ (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9"))) (re.* (re.range "0" "2")))) (str.to.re ".")) (re.++ (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9"))) (re.* (re.range "0" "2")))) (str.to.re ".")) (re.++ (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9"))) (re.* (re.range "0" "2"))))))
(assert (= IPAddr (str.++ (str.++ (str.++ (str.++ "." ".") o2) ".") o1)))
(assert (and (>= (str.len o1) 1) (>= (str.len o2) 1) (>= (str.len o3) 1) (>= (str.len o4) 1)))
(assert (or (= (str.len o1) 1) (= (str.len o2) 1) (= (str.len o3) 1) (= (str.len o4) 1)))
(assert (and (<= (str.len o1) 3) (<= (str.len o2) 3) (<= (str.len o3) 3) (<= 3 (str.len o4))))
(check-sat)

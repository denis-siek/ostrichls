(declare-const IPAddr String)
(declare-const o1 String)
(declare-const o2 String)
(declare-const o3 String)
(declare-const o4 String)
(assert (str.in.re IPAddr (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9"))) (re.* (re.range "0" "2"))) (str.to.re ".")) (re.++ (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9"))) (re.* (re.range "0" "2")))) (str.to.re ".")) (re.++ (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9"))) (re.* (re.range "0" "2")))) (re.* (re.range "0" "2"))) (re.++ (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9"))) (str.to.re ".")))))
(assert (= IPAddr (str.++ (str.++ (str.++ (str.++ (str.++ "." o3) ".") o2) ".") o1)))
(assert (and (>= (str.len o1) 1) (>= (str.len o2) 1) (>= (str.len o3) 1) (>= (str.len o4) 1)))
(assert (or (= (str.len o1) 1) (= (str.len o2) 1) (= (str.len o3) 1) (= (str.len o4) (str.len o3))))
(assert (and (<= (str.len o1) 3) (<= (str.len o2) 3) (<= 1 3) (<= (str.len o4) 3)))
(check-sat)

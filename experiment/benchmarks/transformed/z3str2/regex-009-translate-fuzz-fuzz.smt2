(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "!{EQz:yYBaNd3,_RH!(lGI{lPvG.g'O'\r'""GJ''\t'dt?w*dujHS' '.""B*]{ln!$-%jAqkK' '#LgPbyW,1'\r'oO"))))
(assert (str.in.re x (re.+ (str.to.re "c_9N{'\r'@`Fh-{+' 'c(r&v'\n'xWUk6^&Av%a6m#/!9@0?~;ShZfS^mT0;DZF|b;yBM2,I7ZRr'(Rf3'\x0b'WTkn4KYsDBoY-S|OL1i""RoJ_XZ:k)=h?f@K/'\x0b''\r'Vm^~' ''\x0b''(' '+RX{2t1`[*ZB+Col[\\~K'\r'^6ZggS|14H|Du#W),G8y*mQ6qNOgK:^GZP""XPhArgX'\r''\n'MQ[w-'\r'$W?'\t'm'\x0b'-k_'\r'jq?#(PCz\\n' 'S'\n'R&4OVjMRvV[9,}""`l@a5+=9a6G'\t'0,$X_YGmq3'\t'' 'Uf@6..='\x0c'Gs5V`8q'\t''K""7`ZkKxH1W<W@fe2iJ5I}j~\\'\r'B' ''\x0b'NX%0>t-]/Jf/_tf'\x0b'-"))))
(assert (> (str.len x) 51))
(assert (< (str.len x) 59))
(check-sat)
(get-model)

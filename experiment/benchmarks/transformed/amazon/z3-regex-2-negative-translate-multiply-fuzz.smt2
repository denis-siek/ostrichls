(declare-const S String)
(assert (str.in.re S (re.++ (str.to.re "YCr'\t''\t'>)+~Tz""nh'\x0b'n""v>%o2.CM`U;y1h'\n'pckE`'\x0c'fv'\x0b'V""+?'\r'~`''\r'opU,!3>/""+pr0Z3zXlxpm83'\t'k`'\n':qz''\r'''''1-Iug#Poo4C*5KxIL$vk:SZA%B'""kPQ|m0U}'\t'av>'\x0b'i9ZYVo[=taqiS'\n'Yy*0Sm2E0,D4!('\n'uoo''\r'FlPb'--u$J6'%J'\n'^CLDMG[Wk{P%fN'\t'1' '9TzW$^Z'\r'&w$5KM(`\\Yi'\x0b'$+$rUyT|EfW?/.[/""5'\r'i;v<5Bn' 'wU.)5L@P~'\x0b'nlq8'\x0b'u,UR?}_""ITG#nu|q!D'\r'B3+'$") re.allchar)))
(assert (not (str.in.re S (re.union (re.++ (re.union (str.to.re "'''\r'6'\r'pEG$'\r'BK.Eat':kA)Yj:,0zW'\r'jD2~5=O5}O}[J(RZo''\r''''!0X~@Ye>k'\x0b'`mWjQC+JS2v~;u{_o*M'\n'pWEi'Hmww{^Zp'\x0b''\x0b'6G#*\\i]51K.<(F3<Kp2Y7T-'\n'Ga'd.' 'dt44#~Q+24") re.allchar) (str.to.re "$P$")) re.allchar))))
(check-sat)
(get-model)

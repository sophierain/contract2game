Main [Contract (Definition (AlexPn 15 1 16) "A" constructor() [] (Creates [AssignVal (StorageVar (AlexPn 58 5 9) uint256 "x") (IntLit (AlexPn 63 5 14) 0)]) [] []) [],Contract (Definition (AlexPn 81 7 16) "B" constructor() [] (Creates [AssignVal (StorageVar (AlexPn 124 11 9) uint256 "y") (IntLit (AlexPn 129 11 14) 0),AssignVal (StorageVar (AlexPn 136 12 6) A "a") (ECreate (AlexPn 148 12 18) "A" [])]) [] []) [Transition (AlexPn 153 14 1) "remote" "B" set_remote(uint256 z) [Iff (AlexPn 205 17 1) [EEq (AlexPn 222 18 14) (EnvExp (AlexPn 212 18 4) Callvalue) (IntLit (AlexPn 225 18 17) 0)]] (Direct (Post [Rewrite (EField (AlexPn 240 21 5) (EVar (AlexPn 239 21 4) "a") "x") (EUTEntry (EVar (AlexPn 246 21 11) "z"))] Nothing)) [],Transition (AlexPn 249 23 1) "multi" "B" set_remote2(uint256 z) [Iff (AlexPn 301 26 1) [EEq (AlexPn 318 27 14) (EnvExp (AlexPn 308 27 4) Callvalue) (IntLit (AlexPn 321 27 17) 0)]] (Direct (Post [Rewrite (EVar (AlexPn 335 30 4) "y") (IntLit (AlexPn 340 30 9) 1),Rewrite (EField (AlexPn 346 31 5) (EVar (AlexPn 345 31 4) "a") "x") (EUTEntry (EVar (AlexPn 352 31 11) "z"))] Nothing)) []]]
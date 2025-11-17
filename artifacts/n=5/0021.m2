                                                                      2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y  - y y  - y y , y , y , y , y , y , y )}
                              4 5    4 6    5 6   1 2    1 3    2 3   1   2   3   4   5   6
                                2   2         2   2   2         2
          AOTinIdeal => ideal (y , y , y y , y , y , y , y y , y )
                                6   5   4 5   4   3   2   1 2   1
          graph => {set {0, 2}, set {2, 4}, set {0, 4}, set {1, 3}, set {3, 4}, set {1, 4}}
                                 2      3     4
          hSeries => 1 + 6T + 13T  + 12T  + 4T
          hyperplanes => {a - c, c - e, a - e, b - d, d - e, b - e}
          numVariables => 6
          WLPfull => "A does not have WLP at A_2"
          WLPin => "A does not have WLP at A_2"


R = QQ[y_1..y_6]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_4*y_5-y_4*y_6-y_5*y_6, y_1*y_2-y_1*y_3-y_2*y_3, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_6^2, y_5^2, y_4*y_5, y_4^2, y_3^2, y_2^2, y_1*y_2, y_1^2}})
G = graph {set {0, 2}, set {2, 4}, set {0, 4}, set {1, 3}, set {3, 4}, set {1, 4}}

                                                                                     2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y )}
                              1 2    1 4    2 4   3 4 5    3 4 6    3 5 6    4 5 6   1   2   3   4   5   6
                                2   2   2   2   2         2
          AOTinIdeal => ideal (y , y , y , y , y , y y , y , y y y )
                                6   5   4   3   2   1 2   1   3 4 5
          graph => {set {0, 2}, set {2, 4}, set {0, 3}, set {0, 4}, set {1, 3}, set {1, 4}}
                                 2      3     4
          hSeries => 1 + 6T + 14T  + 15T  + 6T
          hyperplanes => {a - c, c - e, a - d, a - e, b - d, b - e}
          numVariables => 6
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_2"


R = QQ[y_1..y_6]
AOTideal = ideal map(R^1,R^{{-2}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_1*y_2-y_1*y_4-y_2*y_4, y_3*y_4*y_5-y_3*y_4*y_6-y_3*y_5*y_6+y_4*y_5*y_6, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}},{{y_6^2, y_5^2, y_4^2, y_3^2, y_2^2, y_1*y_2, y_1^2, y_3*y_4*y_5}})
G = graph {set {0, 2}, set {2, 4}, set {0, 3}, set {0, 4}, set {1, 3}, set {1, 4}}

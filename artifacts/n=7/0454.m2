                                                                                                        2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  + y y , y y y y  - y y y y  + y y y y  - y y y y  - y y y y , y , y , y , y , y , y , y , y )}
                              2 3    2 5    3 5   4 5 6 7    4 5 6 8    4 5 7 8    4 6 7 8    5 6 7 8   1   2   3   4   5   6   7   8
                                2   2   2   2   2   2         2   2
          AOTinIdeal => ideal (y , y , y , y , y , y , y y , y , y , y y y y )
                                8   7   6   5   4   3   2 3   2   1   4 5 6 7
          graph => {set {0, 3}, set {0, 4}, set {0, 6}, set {1, 4}, set {4, 6}, set {1, 5}, set {2, 5}, set {2, 6}}
                                 2      3      4      5     6
          hSeries => 1 + 8T + 27T  + 50T  + 54T  + 32T  + 8T
          hyperplanes => {a - d, a - e, a - g, b - e, e - g, b - f, c - f, c - g}
          numVariables => 8
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_8]
AOTideal = ideal map(R^1,R^{{-2}, {-4}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_2*y_3-y_2*y_5+y_3*y_5, y_4*y_5*y_6*y_7-y_4*y_5*y_6*y_8+y_4*y_5*y_7*y_8-y_4*y_6*y_7*y_8-y_5*y_6*y_7*y_8, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-4}},{{y_8^2, y_7^2, y_6^2, y_5^2, y_4^2, y_3^2, y_2*y_3, y_2^2, y_1^2, y_4*y_5*y_6*y_7}})
G = graph {set {0, 3}, set {0, 4}, set {0, 6}, set {1, 4}, set {4, 6}, set {1, 5}, set {2, 5}, set {2, 6}}

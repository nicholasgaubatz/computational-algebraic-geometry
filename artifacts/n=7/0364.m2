                                                                                     2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y )}
                              4 5    4 6    5 6   2 3 7    2 3 8    2 7 8    3 7 8   1   2   3   4   5   6   7   8
                                2   2   2   2         2   2   2   2
          AOTinIdeal => ideal (y , y , y , y , y y , y , y , y , y , y y y )
                                8   7   6   5   4 5   4   3   2   1   2 3 7
          graph => {set {0, 3}, set {0, 5}, set {0, 6}, set {1, 4}, set {4, 6}, set {1, 6}, set {2, 5}, set {2, 6}}
                                 2      3      4      5     6
          hSeries => 1 + 8T + 27T  + 49T  + 50T  + 27T  + 6T
          hyperplanes => {a - d, a - f, a - g, b - e, e - g, b - g, c - f, c - g}
          numVariables => 8
          WLPfull => "A does not have WLP at A_3"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_8]
AOTideal = ideal map(R^1,R^{{-2}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_4*y_5-y_4*y_6-y_5*y_6, y_2*y_3*y_7-y_2*y_3*y_8-y_2*y_7*y_8+y_3*y_7*y_8, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}},{{y_8^2, y_7^2, y_6^2, y_5^2, y_4*y_5, y_4^2, y_3^2, y_2^2, y_1^2, y_2*y_3*y_7}})
G = graph {set {0, 3}, set {0, 5}, set {0, 6}, set {1, 4}, set {4, 6}, set {1, 6}, set {2, 5}, set {2, 6}}

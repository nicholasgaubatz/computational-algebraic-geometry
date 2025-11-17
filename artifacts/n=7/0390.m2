                                                                                                                                                           2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y )}
                              1 2    1 4    2 4   6 7 8    6 7 9    6 8 9    7 8 9   3 4 8    3 4 9    3 8 9    4 8 9   3 4 6    3 4 7    3 6 7    4 6 7   1   2   3   4   5   6   7   8   9
                                2   2   2   2   2   2   2   2         2
          AOTinIdeal => ideal (y , y , y , y , y , y , y , y , y y , y , y y y , y y y , y y y )
                                9   8   7   6   5   4   3   2   1 2   1   6 7 8   3 4 8   3 4 6
          graph => {set {0, 3}, set {3, 6}, set {0, 5}, set {0, 6}, set {1, 4}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
                                 2      3      4      5      6
          hSeries => 1 + 9T + 35T  + 74T  + 88T  + 55T  + 14T
          hyperplanes => {a - d, d - g, a - f, a - g, b - e, b - f, b - g, c - f, c - g}
          numVariables => 9
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_9]
AOTideal = ideal map(R^1,R^{{-2}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_1*y_2-y_1*y_4-y_2*y_4, y_6*y_7*y_8-y_6*y_7*y_9-y_6*y_8*y_9+y_7*y_8*y_9, y_3*y_4*y_8-y_3*y_4*y_9-y_3*y_8*y_9+y_4*y_8*y_9, y_3*y_4*y_6-y_3*y_4*y_7-y_3*y_6*y_7+y_4*y_6*y_7, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}},{{y_9^2, y_8^2, y_7^2, y_6^2, y_5^2, y_4^2, y_3^2, y_2^2, y_1*y_2, y_1^2, y_6*y_7*y_8, y_3*y_4*y_8, y_3*y_4*y_6}})
G = graph {set {0, 3}, set {3, 6}, set {0, 5}, set {0, 6}, set {1, 4}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}

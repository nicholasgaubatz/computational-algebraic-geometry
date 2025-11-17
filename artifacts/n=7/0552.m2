                                                                                                                                                 2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  + y y , y y  - y y  + y y , y y  - y y  - y y , y y  - y y  - y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y )}
                              7 8    7 9    8 9   5 6    5 9    6 9   3 4    3 8    4 8   2 4    2 6    4 6   2 3 5    2 3 7    2 5 7    3 5 7   1   2   3   4   5   6   7   8   9
                                2   2         2   2         2   2               2   2   2
          AOTinIdeal => ideal (y , y , y y , y , y , y y , y , y , y y , y y , y , y , y , y y y , y y y )
                                9   8   7 8   7   6   5 6   5   4   3 4   2 4   3   2   1   2 3 6   2 3 5
          graph => {set {0, 3}, set {1, 4}, set {2, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}, set {5, 6}}
                                 2      3      4      5
          hSeries => 1 + 9T + 32T  + 55T  + 45T  + 14T
          hyperplanes => {a - d, b - e, c - e, e - g, b - f, b - g, c - f, c - g, f - g}
          numVariables => 9
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_9]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_7*y_8-y_7*y_9+y_8*y_9, y_5*y_6-y_5*y_9+y_6*y_9, y_3*y_4-y_3*y_8-y_4*y_8, y_2*y_4-y_2*y_6-y_4*y_6, y_2*y_3*y_5-y_2*y_3*y_7-y_2*y_5*y_7+y_3*y_5*y_7, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}},{{y_9^2, y_8^2, y_7*y_8, y_7^2, y_6^2, y_5*y_6, y_5^2, y_4^2, y_3*y_4, y_2*y_4, y_3^2, y_2^2, y_1^2, y_2*y_3*y_6, y_2*y_3*y_5}})
G = graph {set {0, 3}, set {1, 4}, set {2, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}, set {5, 6}}

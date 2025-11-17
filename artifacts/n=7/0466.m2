                                                                                          2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  + y y , y y  - y y  - y y , y y  - y y  + y y , y , y , y , y , y , y , y , y , y )   }
                              6 7    6 9    7 9   4 5    4 7    5 7   2 3    2 5    3 5   1   2   3   4   5   6   7   8   9
                                2   2   2         2   2         2   2         2   2
          AOTinIdeal => ideal (y , y , y , y y , y , y , y y , y , y , y y , y , y )
                                9   8   7   6 7   6   5   4 5   4   3   2 3   2   1
          graph => {set {0, 3}, set {0, 4}, set {0, 6}, set {1, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {5, 6}}
                                 2      3      4      5     6
          hSeries => 1 + 9T + 33T  + 63T  + 66T  + 36T  + 8T
          hyperplanes => {a - d, a - e, a - g, b - e, e - g, b - f, b - g, c - f, f - g}
          numVariables => 9
          WLPfull => "A does not have WLP at A_3"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_9]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_6*y_7-y_6*y_9+y_7*y_9, y_4*y_5-y_4*y_7-y_5*y_7, y_2*y_3-y_2*y_5+y_3*y_5, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_9^2, y_8^2, y_7^2, y_6*y_7, y_6^2, y_5^2, y_4*y_5, y_4^2, y_3^2, y_2*y_3, y_2^2, y_1^2}})
G = graph {set {0, 3}, set {0, 4}, set {0, 6}, set {1, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {5, 6}}

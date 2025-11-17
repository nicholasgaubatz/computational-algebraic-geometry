                                                                                                                                            2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y  - y y  - y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y )}
                              1 3    1 5    3 5   1 2    1 4    2 4   4 5 6    4 5 7    4 6 7    5 6 7   2 3 6    2 3 7    2 6 7    3 6 7   1   2   3   4   5   6   7   8   9
                                2   2   2   2   2   2   2         2         2
          AOTinIdeal => ideal (y , y , y , y , y , y , y , y y , y , y y , y , y y y , y y y , y y y )
                                9   8   7   6   5   4   3   1 3   2   1 2   1   4 5 6   2 3 6   2 3 4
          graph => {set {0, 4}, set {4, 5}, set {4, 6}, set {0, 5}, set {0, 6}, set {1, 5}, set {1, 6}, set {2, 6}, set {3, 6}}
                                 2      3      4      5      6
          hSeries => 1 + 9T + 34T  + 68T  + 75T  + 43T  + 10T
          hyperplanes => {a - e, e - f, e - g, a - f, a - g, b - f, b - g, c - g, d - g}
          numVariables => 9
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_9]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_1*y_3-y_1*y_5-y_3*y_5, y_1*y_2-y_1*y_4-y_2*y_4, y_4*y_5*y_6-y_4*y_5*y_7-y_4*y_6*y_7+y_5*y_6*y_7, y_2*y_3*y_6-y_2*y_3*y_7-y_2*y_6*y_7+y_3*y_6*y_7, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}},{{y_9^2, y_8^2, y_7^2, y_6^2, y_5^2, y_4^2, y_3^2, y_1*y_3, y_2^2, y_1*y_2, y_1^2, y_4*y_5*y_6, y_2*y_3*y_6, y_2*y_3*y_4}})
G = graph {set {0, 4}, set {4, 5}, set {4, 6}, set {0, 5}, set {0, 6}, set {1, 5}, set {1, 6}, set {2, 6}, set {3, 6}}

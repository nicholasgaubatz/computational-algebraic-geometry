                                                                                                                                  2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  + y y , y y  - y y  + y y , y y  - y y  - y y , y y  - y y  - y y , y y  - y y  - y y , y , y , y , y , y , y , y , y , y )}
                              5 6    5 9    6 9   3 4    3 9    4 9   2 4    2 7    4 7   1 4    1 6    4 6   1 3    1 5    3 5   1   2   3   4   5   6   7   8   9
                                2   2   2   2         2   2                     2         2   2
          AOTinIdeal => ideal (y , y , y , y , y y , y , y , y y , y y , y y , y , y y , y , y , y y y , y y y , y y y y )
                                9   8   7   6   5 6   5   4   3 4   2 4   1 4   3   1 3   2   1   2 3 7   1 2 6   1 2 5 7
          graph => {set {0, 4}, set {1, 4}, set {4, 5}, set {4, 6}, set {0, 5}, set {0, 6}, set {1, 6}, set {2, 5}, set {5, 6}}
                                 2      3      4      5
          hSeries => 1 + 9T + 31T  + 51T  + 40T  + 12T
          hyperplanes => {a - e, b - e, e - f, e - g, a - f, a - g, b - g, c - f, f - g}
          numVariables => 9
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_9]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_5*y_6-y_5*y_9+y_6*y_9, y_3*y_4-y_3*y_9+y_4*y_9, y_2*y_4-y_2*y_7-y_4*y_7, y_1*y_4-y_1*y_6-y_4*y_6, y_1*y_3-y_1*y_5-y_3*y_5, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-4}},{{y_9^2, y_8^2, y_7^2, y_6^2, y_5*y_6, y_5^2, y_4^2, y_3*y_4, y_2*y_4, y_1*y_4, y_3^2, y_1*y_3, y_2^2, y_1^2, y_2*y_3*y_7, y_1*y_2*y_6, y_1*y_2*y_5*y_7}})
G = graph {set {0, 4}, set {1, 4}, set {4, 5}, set {4, 6}, set {0, 5}, set {0, 6}, set {1, 6}, set {2, 5}, set {5, 6}}

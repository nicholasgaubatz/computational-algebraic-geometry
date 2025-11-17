                                                                                                                                                                              2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y y  - y y y y  - y y y y  + y y y y  - y y y y , y , y , y , y , y , y , y , y , y )}
                              4 6    4 8    6 8   4 5 7    4 5 9    4 7 9    5 7 9   2 3 7    2 3 8    2 7 8    3 7 8   2 3 5 6    2 3 5 9    2 3 6 9    2 5 6 9    3 5 6 9   1   2   3   4   5   6   7   8   9
                                2   2   2   2         2   2   2   2   2
          AOTinIdeal => ideal (y , y , y , y , y y , y , y , y , y , y , y y y , y y y , y y y y , y y y y , y y y y y )
                                9   8   7   6   4 6   5   4   3   2   1   4 5 7   2 3 7   5 6 7 8   2 3 5 6   2 3 4 5 8
          graph => {set {0, 3}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}}
                                 2      3      4      5      6
          hSeries => 1 + 9T + 35T  + 75T  + 92T  + 60T  + 16T
          hyperplanes => {a - d, a - f, a - g, b - e, c - e, e - g, b - f, b - g, c - f}
          numVariables => 9
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_9]
AOTideal = ideal map(R^1,R^{{-2}, {-3}, {-3}, {-4}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_4*y_6-y_4*y_8-y_6*y_8, y_4*y_5*y_7-y_4*y_5*y_9-y_4*y_7*y_9+y_5*y_7*y_9, y_2*y_3*y_7-y_2*y_3*y_8-y_2*y_7*y_8+y_3*y_7*y_8, y_2*y_3*y_5*y_6-y_2*y_3*y_5*y_9-y_2*y_3*y_6*y_9+y_2*y_5*y_6*y_9-y_3*y_5*y_6*y_9, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-4}, {-4}, {-5}},{{y_9^2, y_8^2, y_7^2, y_6^2, y_4*y_6, y_5^2, y_4^2, y_3^2, y_2^2, y_1^2, y_4*y_5*y_7, y_2*y_3*y_7, y_5*y_6*y_7*y_8, y_2*y_3*y_5*y_6, y_2*y_3*y_4*y_5*y_8}})
G = graph {set {0, 3}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}}

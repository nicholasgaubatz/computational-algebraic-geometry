                                                                                                                                                                          2   2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  + y y , y y  - y y  + y y , y y  - y y  + y y , y y  - y y  - y y , y y  - y y  - y y , y y  - y y  - y y , y y  - y y  - y y , y , y , y , y , y , y , y , y , y , y  )}
                              7 8    7 9    8 9   5 6    5 9    6 9   3 4    3 9    4 9   2 4    2 8    4 8   1 4    1 6    4 6   2 3    2 7    3 7   1 3    1 5    3 5   1   2   3   4   5   6   7   8   9   10
                                2    2   2         2   2         2   2                     2               2   2
          AOTinIdeal => ideal (y  , y , y , y y , y , y , y y , y , y , y y , y y , y y , y , y y , y y , y , y , y y y , y y y )
                                10   9   8   7 8   7   6   5 6   5   4   3 4   2 4   1 4   3   2 3   1 3   2   1   1 2 6   1 2 5
          graph => {set {0, 3}, set {1, 3}, set {3, 4}, set {3, 5}, set {0, 4}, set {0, 5}, set {1, 4}, set {1, 5}, set {4, 5}, set {2, 5}}
                                  2      3      4      5
          hSeries => 1 + 10T + 38T  + 68T  + 57T  + 18T
          hyperplanes => {a - d, b - d, d - e, d - f, a - e, a - f, b - e, b - f, e - f, c - f}
          numVariables => 10
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_10]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_7*y_8-y_7*y_9+y_8*y_9, y_5*y_6-y_5*y_9+y_6*y_9, y_3*y_4-y_3*y_9+y_4*y_9, y_2*y_4-y_2*y_8-y_4*y_8, y_1*y_4-y_1*y_6-y_4*y_6, y_2*y_3-y_2*y_7-y_3*y_7, y_1*y_3-y_1*y_5-y_3*y_5, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}},{{y_10^2, y_9^2, y_8^2, y_7*y_8, y_7^2, y_6^2, y_5*y_6, y_5^2, y_4^2, y_3*y_4, y_2*y_4, y_1*y_4, y_3^2, y_2*y_3, y_1*y_3, y_2^2, y_1^2, y_1*y_2*y_6, y_1*y_2*y_5}})
G = graph {set {0, 3}, set {1, 3}, set {3, 4}, set {3, 5}, set {0, 4}, set {0, 5}, set {1, 4}, set {1, 5}, set {4, 5}, set {2, 5}}

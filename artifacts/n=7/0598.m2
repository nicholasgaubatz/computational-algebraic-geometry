                                                                                                                                        2   2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y   + y y  , y y  - y y   + y y  , y y  - y y  - y y , y y  - y y  - y y , y y  - y y   + y y  , y , y , y , y , y , y , y , y , y , y  )}
                              8 9    8 10    9 10   6 7    6 10    7 10   4 7    4 9    7 9   4 6    4 8    6 8   2 3    2 10    3 10   1   2   3   4   5   6   7   8   9   10
                                2    2         2   2               2         2   2   2         2   2
          AOTinIdeal => ideal (y  , y , y y , y , y , y y , y y , y , y y , y , y , y , y y , y , y )
                                10   9   8 9   8   7   6 7   4 7   6   4 6   5   4   3   2 3   2   1
          graph => {set {0, 3}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 5}, set {4, 6}, set {1, 5}, set {1, 6}, set {5, 6}}
                                  2      3      4      5      6
          hSeries => 1 + 10T + 40T  + 82T  + 91T  + 52T  + 12T
          hyperplanes => {a - d, a - f, a - g, b - e, c - e, e - f, e - g, b - f, b - g, f - g}
          numVariables => 10
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_10]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_8*y_9-y_8*y_10+y_9*y_10, y_6*y_7-y_6*y_10+y_7*y_10, y_4*y_7-y_4*y_9-y_7*y_9, y_4*y_6-y_4*y_8-y_6*y_8, y_2*y_3-y_2*y_10+y_3*y_10, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_10^2, y_9^2, y_8*y_9, y_8^2, y_7^2, y_6*y_7, y_4*y_7, y_6^2, y_4*y_6, y_5^2, y_4^2, y_3^2, y_2*y_3, y_2^2, y_1^2}})
G = graph {set {0, 3}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 5}, set {4, 6}, set {1, 5}, set {1, 6}, set {5, 6}}

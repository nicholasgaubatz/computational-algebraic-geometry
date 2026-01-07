                                                                                                                                                                            2   2   2   2   2   2   2   2   2   2    2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y  - y y   + y y  , y y  - y y   + y y  , y y  - y y  - y y , y y  - y y  - y y , y y y  - y y y   - y y y   + y y y  , y , y , y , y , y , y , y , y , y , y  , y  )}
                              7 8    7 9    8 9   4 6    4 11    6 11   2 3    2 11    3 11   1 3    1 6    3 6   1 2    1 4    2 4   5 6 9    5 6 10    5 9 10    6 9 10   1   2   3   4   5   6   7   8   9   10   11
                                2    2    2   2         2   2         2   2   2               2         2
          AOTinIdeal => ideal (y  , y  , y , y , y y , y , y , y y , y , y , y , y y , y y , y , y y , y , y y y , y y y y  )
                                11   10   9   8   7 8   7   6   4 6   5   4   3   2 3   1 3   2   1 2   1   5 6 9   4 5 9 10
          graph => {set {0, 2}, set {2, 4}, set {2, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 3}, set {3, 5}, set {1, 5}, set {1, 6}, set {4, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 11T + 50T  + 121T  + 165T  + 120T  + 36T
          hyperplanes => {a - c, c - e, c - g, a - e, a - f, a - g, b - d, d - f, b - f, b - g, e - g}
          numVariables => 11
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_11]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_7*y_8-y_7*y_9-y_8*y_9, y_4*y_6-y_4*y_11+y_6*y_11, y_2*y_3-y_2*y_11+y_3*y_11, y_1*y_3-y_1*y_6-y_3*y_6, y_1*y_2-y_1*y_4-y_2*y_4, y_5*y_6*y_9-y_5*y_6*y_10-y_5*y_9*y_10+y_6*y_9*y_10, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-4}},{{y_11^2, y_10^2, y_9^2, y_8^2, y_7*y_8, y_7^2, y_6^2, y_4*y_6, y_5^2, y_4^2, y_3^2, y_2*y_3, y_1*y_3, y_2^2, y_1*y_2, y_1^2, y_5*y_6*y_9, y_4*y_5*y_9*y_10}})
G = graph {set {0, 2}, set {2, 4}, set {2, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 3}, set {3, 5}, set {1, 5}, set {1, 6}, set {4, 6}}

                                                                                                                                                                                                                                                                         2   2   2   2   2   2   2   2   2   2    2
HashTable{AOTideal => ideal (y y   - y y   + y  y  , y y  - y y   + y y  , y y  - y y   + y y  , y y  - y y   - y y  , y y  - y y  - y y , y y  - y y  - y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y , y  , y  )}
                              9 10    9 11    10 11   7 8    7 11    8 11   5 6    5 11    6 11   3 4    3 10    4 10   2 4    2 8    4 8   1 4    1 6    4 6   2 3 7    2 3 9    2 7 9    3 7 9   1 3 5    1 3 9    1 5 9    3 5 9   1 2 5    1 2 7    1 5 7    2 5 7   1   2   3   4   5   6   7   8   9   10   11
                                2    2           2   2         2   2         2   2                     2   2   2
          AOTinIdeal => ideal (y  , y  , y y  , y , y , y y , y , y , y y , y , y , y y , y y , y y , y , y , y , y y y , y y y , y y y , y y y , y y y , y y y )
                                11   10   9 10   9   8   7 8   7   6   5 6   5   4   3 4   2 4   1 4   3   2   1   2 3 8   2 3 7   1 3 6   1 2 6   1 3 5   1 2 5
          graph => {set {0, 3}, set {1, 3}, set {2, 3}, set {3, 5}, set {0, 4}, set {0, 5}, set {1, 4}, set {1, 5}, set {2, 4}, set {2, 5}, set {4, 5}}
                                  2       3       4      5
          hSeries => 1 + 11T + 49T  + 108T  + 115T  + 46T
          hyperplanes => {a - d, b - d, c - d, d - f, a - e, a - f, b - e, b - f, c - e, c - f, e - f}
          numVariables => 11
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_3"


R = QQ[y_1..y_11]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_9*y_10-y_9*y_11+y_10*y_11, y_7*y_8-y_7*y_11+y_8*y_11, y_5*y_6-y_5*y_11+y_6*y_11, y_3*y_4-y_3*y_10-y_4*y_10, y_2*y_4-y_2*y_8-y_4*y_8, y_1*y_4-y_1*y_6-y_4*y_6, y_2*y_3*y_7-y_2*y_3*y_9-y_2*y_7*y_9+y_3*y_7*y_9, y_1*y_3*y_5-y_1*y_3*y_9-y_1*y_5*y_9+y_3*y_5*y_9, y_1*y_2*y_5-y_1*y_2*y_7-y_1*y_5*y_7+y_2*y_5*y_7, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}},{{y_11^2, y_10^2, y_9*y_10, y_9^2, y_8^2, y_7*y_8, y_7^2, y_6^2, y_5*y_6, y_5^2, y_4^2, y_3*y_4, y_2*y_4, y_1*y_4, y_3^2, y_2^2, y_1^2, y_2*y_3*y_8, y_2*y_3*y_7, y_1*y_3*y_6, y_1*y_2*y_6, y_1*y_3*y_5, y_1*y_2*y_5}})
G = graph {set {0, 3}, set {1, 3}, set {2, 3}, set {3, 5}, set {0, 4}, set {0, 5}, set {1, 4}, set {1, 5}, set {2, 4}, set {2, 5}, set {4, 5}}

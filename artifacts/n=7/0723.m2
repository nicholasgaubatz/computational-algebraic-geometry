                                                                                                                                                                                                                                                                                                                                                        2   2   2   2   2   2   2   2   2   2    2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y  - y y  + y y , y y  - y y  - y y , y y y   - y y y   - y y  y   + y y  y  , y y y  - y y y  - y y y  + y y y , y y y y   - y y y y   - y y y  y   + y y y  y   - y y y  y  , y y y y   - y y y y   + y y y  y   - y y y  y   - y y y  y  , y y y y  - y y y y  + y y y y  - y y y y  - y y y y , y , y , y , y , y , y , y , y , y , y  , y  )}
                              6 7    6 9    7 9   2 3    2 7    3 7   1 2    1 4    2 4   8 9 10    8 9 11    8 10 11    9 10 11   4 5 6    4 5 8    4 6 8    5 6 8   4 5 7 10    4 5 7 11    4 5 10 11    4 7 10 11    5 7 10 11   1 3 5 10    1 3 5 11    1 3 10 11    1 5 10 11    3 5 10 11   1 3 5 8    1 3 5 9    1 3 8 9    1 5 8 9    3 5 8 9   1   2   3   4   5   6   7   8   9   10   11
                                2    2    2   2   2         2   2   2   2         2         2
          AOTinIdeal => ideal (y  , y  , y , y , y , y y , y , y , y , y , y y , y , y y , y , y y y  , y y y , y y y , y y y y  , y y y y  , y y y y , y y y y )
                                11   10   9   8   7   6 7   6   5   4   3   2 3   2   1 2   1   8 9 10   4 5 6   1 3 4   4 5 7 10   1 3 5 10   4 5 7 8   1 3 5 8
          graph => {set {0, 3}, set {3, 4}, set {3, 6}, set {0, 4}, set {0, 5}, set {1, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 11T + 52T  + 136T  + 206T  + 168T  + 56T
          hyperplanes => {a - d, d - e, d - g, a - e, a - f, b - e, e - g, b - f, b - g, c - f, c - g}
          numVariables => 11
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_11]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-3}, {-3}, {-4}, {-4}, {-4}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_6*y_7-y_6*y_9-y_7*y_9, y_2*y_3-y_2*y_7+y_3*y_7, y_1*y_2-y_1*y_4-y_2*y_4, y_8*y_9*y_10-y_8*y_9*y_11-y_8*y_10*y_11+y_9*y_10*y_11, y_4*y_5*y_6-y_4*y_5*y_8-y_4*y_6*y_8+y_5*y_6*y_8, y_4*y_5*y_7*y_10-y_4*y_5*y_7*y_11-y_4*y_5*y_10*y_11+y_4*y_7*y_10*y_11-y_5*y_7*y_10*y_11, y_1*y_3*y_5*y_10-y_1*y_3*y_5*y_11+y_1*y_3*y_10*y_11-y_1*y_5*y_10*y_11-y_3*y_5*y_10*y_11, y_1*y_3*y_5*y_8-y_1*y_3*y_5*y_9+y_1*y_3*y_8*y_9-y_1*y_5*y_8*y_9-y_3*y_5*y_8*y_9, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-4}, {-4}, {-4}, {-4}},{{y_11^2, y_10^2, y_9^2, y_8^2, y_7^2, y_6*y_7, y_6^2, y_5^2, y_4^2, y_3^2, y_2*y_3, y_2^2, y_1*y_2, y_1^2, y_8*y_9*y_10, y_4*y_5*y_6, y_1*y_3*y_4, y_4*y_5*y_7*y_10, y_1*y_3*y_5*y_10, y_4*y_5*y_7*y_8, y_1*y_3*y_5*y_8}})
G = graph {set {0, 3}, set {3, 4}, set {3, 6}, set {0, 4}, set {0, 5}, set {1, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}

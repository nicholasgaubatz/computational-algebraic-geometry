                                                                                                                                                                                                                                                                                                      2   2   2   2   2   2   2   2   2   2    2
HashTable{AOTideal => ideal (y y  - y y   + y y  , y y  - y y  - y y , y y  - y y  - y y , y y  - y y  - y y , y y y y   - y y y y   - y y y  y   + y y y  y   - y y y  y  , y y y y   - y y y y   - y y y  y   + y y y  y   - y y y  y  , y y y y  - y y y y   + y y y y   - y y y y   - y y y y  , y , y , y , y , y , y , y , y , y , y  , y  )}
                              5 6    5 10    6 10   2 4    2 8    4 8   1 4    1 6    4 6   2 3    2 7    3 7   7 8 9 10    7 8 9 11    7 8 10 11    7 9 10 11    8 9 10 11   3 4 9 10    3 4 9 11    3 4 10 11    3 9 10 11    4 9 10 11   1 3 5 9    1 3 5 11    1 3 9 11    1 5 9 11    3 5 9 11   1   2   3   4   5   6   7   8   9   10   11
                                2    2    2   2   2   2         2   2               2         2   2
          AOTinIdeal => ideal (y  , y  , y , y , y , y , y y , y , y , y y , y y , y , y y , y , y , y y y , y y y , y y y y  , y y y y  , y y y y , y y y y , y y y y , y y y y y  , y y y y y , y y y y y )
                                11   10   9   8   7   6   5 6   5   4   2 4   1 4   3   2 3   2   1   3 4 7   1 2 6   7 8 9 10   3 4 9 10   1 3 5 9   1 2 5 8   1 3 6 7   1 3 6 9 10   1 2 5 7 9   1 3 5 7 8
          graph => {set {0, 3}, set {1, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 6}, set {1, 5}, set {1, 6}, set {2, 4}, set {4, 6}, set {2, 5}}
                                  2       3       4       5      6
          hSeries => 1 + 11T + 51T  + 129T  + 189T  + 151T  + 50T
          hyperplanes => {a - d, b - d, d - f, d - g, a - e, a - g, b - f, b - g, c - e, e - g, c - f}
          numVariables => 11
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_11]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-4}, {-4}, {-4}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_5*y_6-y_5*y_10+y_6*y_10, y_2*y_4-y_2*y_8-y_4*y_8, y_1*y_4-y_1*y_6-y_4*y_6, y_2*y_3-y_2*y_7-y_3*y_7, y_7*y_8*y_9*y_10-y_7*y_8*y_9*y_11-y_7*y_8*y_10*y_11+y_7*y_9*y_10*y_11-y_8*y_9*y_10*y_11, y_3*y_4*y_9*y_10-y_3*y_4*y_9*y_11-y_3*y_4*y_10*y_11+y_3*y_9*y_10*y_11-y_4*y_9*y_10*y_11, y_1*y_3*y_5*y_9-y_1*y_3*y_5*y_11+y_1*y_3*y_9*y_11-y_1*y_5*y_9*y_11-y_3*y_5*y_9*y_11, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-4}, {-4}, {-4}, {-4}, {-4}, {-5}, {-5}, {-5}},{{y_11^2, y_10^2, y_9^2, y_8^2, y_7^2, y_6^2, y_5*y_6, y_5^2, y_4^2, y_2*y_4, y_1*y_4, y_3^2, y_2*y_3, y_2^2, y_1^2, y_3*y_4*y_7, y_1*y_2*y_6, y_7*y_8*y_9*y_10, y_3*y_4*y_9*y_10, y_1*y_3*y_5*y_9, y_1*y_2*y_5*y_8, y_1*y_3*y_6*y_7, y_1*y_3*y_6*y_9*y_10, y_1*y_2*y_5*y_7*y_9, y_1*y_3*y_5*y_7*y_8}})
G = graph {set {0, 3}, set {1, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 6}, set {1, 5}, set {1, 6}, set {2, 4}, set {4, 6}, set {2, 5}}

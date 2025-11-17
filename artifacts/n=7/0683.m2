                                                                                                                                                                                                                                                                          2   2   2   2   2   2   2   2   2   2    2
HashTable{AOTideal => ideal (y y  - y y   + y y  , y y  - y y  - y y , y y  - y y   + y y  , y y  - y y  + y y , y y y   + y y y   - y y  y   - y y  y  , y y y  - y y y   - y y y   + y y y  , y y y  - y y y   - y y y   + y y y  , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y , y  , y  )}
                              8 9    8 11    9 11   5 7    5 9    7 9   3 4    3 11    4 11   2 4    2 7    4 7   6 7 10    6 7 11    6 10 11    7 10 11   5 6 8    5 6 10    5 8 10    6 8 10   2 3 6    2 3 10    2 6 10    3 6 10   2 3 5    2 3 8    2 5 8    3 5 8   1   2   3   4   5   6   7   8   9   10   11
                                2    2    2         2   2         2   2   2               2   2   2
          AOTinIdeal => ideal (y  , y  , y , y y , y , y , y y , y , y , y , y y , y y , y , y , y , y y y  , y y y , y y y , y y y , y y y , y y y y  )
                                11   10   9   8 9   8   7   5 7   6   5   4   3 4   2 4   3   2   1   6 7 10   5 6 8   2 3 7   2 3 6   2 3 5   5 6 9 10
          graph => {set {0, 3}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {5, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 11T + 51T  + 125T  + 168T  + 116T  + 32T
          hyperplanes => {a - d, a - e, a - f, a - g, b - e, c - e, e - g, b - f, b - g, c - f, f - g}
          numVariables => 11
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_11]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_8*y_9-y_8*y_11+y_9*y_11, y_5*y_7-y_5*y_9-y_7*y_9, y_3*y_4-y_3*y_11+y_4*y_11, y_2*y_4-y_2*y_7+y_4*y_7, y_6*y_7*y_10+y_6*y_7*y_11-y_6*y_10*y_11-y_7*y_10*y_11, y_5*y_6*y_8-y_5*y_6*y_10-y_5*y_8*y_10+y_6*y_8*y_10, y_2*y_3*y_6-y_2*y_3*y_10-y_2*y_6*y_10+y_3*y_6*y_10, y_2*y_3*y_5-y_2*y_3*y_8-y_2*y_5*y_8+y_3*y_5*y_8, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-4}},{{y_11^2, y_10^2, y_9^2, y_8*y_9, y_8^2, y_7^2, y_5*y_7, y_6^2, y_5^2, y_4^2, y_3*y_4, y_2*y_4, y_3^2, y_2^2, y_1^2, y_6*y_7*y_10, y_5*y_6*y_8, y_2*y_3*y_7, y_2*y_3*y_6, y_2*y_3*y_5, y_5*y_6*y_9*y_10}})
G = graph {set {0, 3}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 4}, set {2, 4}, set {4, 6}, set {1, 5}, set {1, 6}, set {2, 5}, set {5, 6}}

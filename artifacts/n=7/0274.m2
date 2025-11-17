                                                                                                                                                                2   2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y  - y y  - y y , y y  - y y  - y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y , y  )}
                              2 4    2 7    4 7   1 4    1 6    4 6   1 3    1 5    3 5   5 6 8    5 6 9    5 8 9    6 8 9   3 4 8    3 4 9    3 8 9    4 8 9   1   2   3   4   5   6   7   8   9   10
                                2    2   2   2   2   2   2               2         2   2
          AOTinIdeal => ideal (y  , y , y , y , y , y , y , y y , y y , y , y y , y , y , y y y , y y y , y y y , y y y , y y y y , y y y y , y y y y y )
                                10   9   8   7   6   5   4   2 4   1 4   3   1 3   2   1   5 6 8   3 4 8   1 2 6   3 4 5   2 3 7 8   2 3 5 6   1 2 5 7 8
          graph => {set {0, 4}, set {1, 4}, set {4, 5}, set {4, 6}, set {0, 5}, set {0, 6}, set {1, 6}, set {2, 5}, set {2, 6}, set {3, 6}}
                                  2      3       4      5      6
          hSeries => 1 + 10T + 42T  + 94T  + 117T  + 76T  + 20T
          hyperplanes => {a - e, b - e, e - f, e - g, a - f, a - g, b - g, c - f, c - g, d - g}
          numVariables => 10
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_10]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_2*y_4-y_2*y_7-y_4*y_7, y_1*y_4-y_1*y_6-y_4*y_6, y_1*y_3-y_1*y_5-y_3*y_5, y_5*y_6*y_8-y_5*y_6*y_9-y_5*y_8*y_9+y_6*y_8*y_9, y_3*y_4*y_8-y_3*y_4*y_9-y_3*y_8*y_9+y_4*y_8*y_9, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-4}, {-4}, {-5}},{{y_10^2, y_9^2, y_8^2, y_7^2, y_6^2, y_5^2, y_4^2, y_2*y_4, y_1*y_4, y_3^2, y_1*y_3, y_2^2, y_1^2, y_5*y_6*y_8, y_3*y_4*y_8, y_1*y_2*y_6, y_3*y_4*y_5, y_2*y_3*y_7*y_8, y_2*y_3*y_5*y_6, y_1*y_2*y_5*y_7*y_8}})
G = graph {set {0, 4}, set {1, 4}, set {4, 5}, set {4, 6}, set {0, 5}, set {0, 6}, set {1, 6}, set {2, 5}, set {2, 6}, set {3, 6}}

                                                                      2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y  - y y  - y y , y , y , y , y , y , y , y )       }
                              3 4    3 6    4 6   2 4    2 5    4 5   1   2   3   4   5   6   7
                                2   2   2   2               2   2   2
          AOTinIdeal => ideal (y , y , y , y , y y , y y , y , y , y , y y y )
                                7   6   5   4   3 4   2 4   3   2   1   2 3 5
          graph => {set {0, 4}, set {1, 5}, set {2, 5}, set {5, 6}, set {1, 6}, set {2, 6}, set {3, 6}}
                                 2      3      4     5
          hSeries => 1 + 7T + 19T  + 25T  + 16T  + 4T
          hyperplanes => {a - e, b - f, c - f, f - g, b - g, c - g, d - g}
          numVariables => 7
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_7]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_3*y_4-y_3*y_6-y_4*y_6, y_2*y_4-y_2*y_5-y_4*y_5, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}},{{y_7^2, y_6^2, y_5^2, y_4^2, y_3*y_4, y_2*y_4, y_3^2, y_2^2, y_1^2, y_2*y_3*y_5}})
G = graph {set {0, 4}, set {1, 5}, set {2, 5}, set {5, 6}, set {1, 6}, set {2, 6}, set {3, 6}}

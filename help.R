#################################
########## help functions
#################################

Ispline <- function(x, order, knots) {
  k = order + 1
  m = length(knots)
  n = m - 2 + k
  t = c(rep(1, k) * knots[1], knots[2:(m - 1)], rep(1, 
                                                    k) * knots[m])
  yy1 = array(rep(0, (n + k - 1) * length(x)), dim = c(n + 
                                                         k - 1, length(x)))
  for (l in k:n) {
    yy1[l, ] = (x >= t[l] & x < t[l + 1])/(t[l + 1] - 
                                             t[l])
  }
  yytem1 = yy1
  for (ii in 1:order) {
    yytem2 = array(rep(0, (n + k - 1 - ii) * length(x)), 
                   dim = c(n + k - 1 - ii, length(x)))
    for (i in (k - ii):n) {
      yytem2[i, ] = (ii + 1) * ((x - t[i]) * yytem1[i, 
      ] + (t[i + ii + 1] - x) * yytem1[i + 1, ])/(t[i + 
                                                      ii + 1] - t[i])/ii
    }
    yytem1 = yytem2
  }
  index = rep(0, length(x))
  for (i in 1:length(x)) {
    index[i] = sum(t <= x[i])
  }
  yy = array(rep(0, (n - 1) * length(x)), dim = c(n - 1, 
                                                  length(x)))
  if (order == 1) {
    for (i in 2:n) {
      yy[i - 1, ] = (i < index - order + 1) + (i == 
                                                 index) * (t[i + order + 1] - t[i]) * yytem2[i, 
                                                 ]/(order + 1)
    }
  }
  else {
    for (j in 1:length(x)) {
      for (i in 2:n) {
        if (i < (index[j] - order + 1)) {
          yy[i - 1, j] = 1
        }
        else if ((i <= index[j]) && (i >= (index[j] - 
                                           order + 1))) {
          yy[i - 1, j] = (t[(i + order + 1):(index[j] + 
                                               order + 1)] - t[i:index[j]]) %*% yytem2[i:index[j], 
                                                                                       j]/(order + 1)
        }
        else {
          yy[i - 1, j] = 0
        }
      }
    }
  }
  return(yy)
}

Mspline <- function(x, order, knots) {
  k1 = order
  m = length(knots)
  n1 = m - 2 + k1
  t1 = c(rep(1, k1) * knots[1], knots[2:(m - 1)], rep(1, 
                                                      k1) * knots[m])
  tem1 = array(rep(0, (n1 + k1 - 1) * length(x)), dim = c(n1 + 
                                                            k1 - 1, length(x)))
  for (l in k1:n1) {
    tem1[l, ] = (x >= t1[l] & x < t1[l + 1])/(t1[l + 
                                                   1] - t1[l])
  }
  if (order == 1) {
    mbases = tem1
  }
  else {
    mbases = tem1
    for (ii in 1:(order - 1)) {
      tem = array(rep(0, (n1 + k1 - 1 - ii) * length(x)), 
                  dim = c(n1 + k1 - 1 - ii, length(x)))
      for (i in (k1 - ii):n1) {
        tem[i, ] = (ii + 1) * ((x - t1[i]) * mbases[i, 
        ] + (t1[i + ii + 1] - x) * mbases[i + 1, 
        ])/(t1[i + ii + 1] - t1[i])/ii
      }
      mbases = tem
    }
  }
  return(mbases)
}

poissrndpositive <- function(lambda) {
  q = 200
  t = seq(0, q, 1)
  p = dpois(t, lambda)
  pp = cumsum(p[2:(q + 1)])/(1 - p[1])
  u = runif(1)
  while (u > pp[q]) {
    q = q + 1
    pp[q] = pp[q - 1] + dpois(q, lambda)/(1 - p[1])
  }
  ll = sum(u > pp) + 1
}

positivepoissonrnd<-function(lambda){ 
  samp = rpois(1, lambda)
  while (samp==0) {
    samp = rpois(1, lambda)
  }
  return(samp)
}

theta_fun <- function(x, i, theta, U, zz,mu1,sig_theta, coef_range_theta)
{
  theta[i] <- x
  mu = mu1[i]
  tt<- sum(zz%*%theta*U -log(1+exp(zz%*%theta)))-(x-mu)^2/sig_theta^2/2
  return(tt)
}

ind_fun_theta<- function(x, i, theta, U, zz,mu1,sig_theta, coef_range_theta)
{(x>-coef_range_theta)*(x<coef_range_theta)}

rho_fun <- function(x,r,rho,n1,N,xx,mu,te1,te2,te3,sig_rho,coef_range_rho) 
{
  rho[r]<-x
  mub = mu[r]
  tt<-sum(x*xx[1:n1, r] - te3 * exp(xx[1:n1,] %*% rho)) + sum(xx[(n1+1):N,r]*x*te1)-sum(exp(xx[(n1 + 1):N, ]%*%rho)*te2)-(x-mub)^2/sig_rho^2/2 # prior(beta)=N(0,sig0^2) 
  return(tt)     
}

ind_fun_rho <- function(x,r,rho,n1,N,xx,mu,te1,te2,te3,sig_rho,coef_range_rho)
{(x>-coef_range_rho)*(x<coef_range_rho)}

CPIC.simu<- function(n,alpha, beta,n1)
{
  #data generation
  
  index <- 1:n 
  Z = cbind(rnorm(n,0,1),rbinom(n,1, 0.5))
  W <- runif(n,0,1)
  g <- sin(W*pi)
  
  cuindi<-function(alpha, g, n)
  {
    eta <- Z%*%alpha+g # uncured probability
    prob<-exp(eta)/(1+exp(eta));
    U <- rbinom(n, 1, prob) 
    re= list(U= U, eta =eta)
    return(re)
  }
  U1 <- cuindi(alpha[1,], g,n)$U; eta1 = cuindi(alpha[1,], g,n)$eta
  U2 <- cuindi(alpha[2,], g,n)$U; eta2 = cuindi(alpha[2,], g,n)$eta;
  mean(U1); mean(U2)
  
  X <- cbind(rnorm(n,0,1),rbinom(n,1,0.5))
  V <- runif(n ,0, 1)
  f<- V^2
  
  y <- matrix(rep(0,n), nrow=n, ncol=1)
  L <- matrix(rep(0,n), nrow=n, ncol=1)
  R <- matrix(rep(0,n), nrow=n, ncol=1)
  C <-matrix(1.5, nrow = n, ncol = 1)     # length of study
  u <- runif(n, 0, 1)
  True<- sqrt(-0.5*log(1-u)*exp(-X%*%beta-f))
  icProc<- function(True, C, U)
  {
    lp <-0 ; rp <-rexp(1,5)
    if (U==0) return(c(C, Inf))
    if (U==1)
    {
      if (True >= C)  return(c(C, Inf)) 
      if (True < C & True < rp) return(c(lp,rp))
      if (True < C & True > rp) 
      {
        repeat{ 
          lp <- rp ; rp <- rp+ runif(1,0,0.2)
          if(True>lp & True< rp ) {break}
        }
        return(c(lp, rp))
      }
    }
  }
  intends <-mapply(icProc, True = True, C=C, U=U1)
  y <- ifelse(intends[1,]==0,0,1) ;y <- ifelse(intends[2,]==Inf, 2, y)
  X1 <- data.frame(L = intends[1,], R = intends[2,],T=True,y = y,U=U1,X = X,V = V, Z = Z, W = W,eta=eta1)
  if(n1>0){
    IC=rep(1,n);X1=cbind(X1,IC)
    ind=sample(which(X1$U==1&X1$y==1),min(n1,sum(X1$U==1&X1$y==1)))
    X1$L[ind]=X1$T[ind];X1$R[ind]=X1$T[ind];
    X1$y[ind]=3;X1$IC[ind]=0}
  X1 <- X1 %>% arrange(IC)
  if(n1==0){
    X1 = X1
  }
  X1 = cbind(X1,IC)
  
  intends <-mapply(icProc, True = True, C=C, U=U2)
  y <- ifelse(intends[1,]==0,0,1) ;y <- ifelse(intends[2,]==Inf, 2, y)
  X2 <- data.frame(L = intends[1,], R = intends[2,],T=True,y = y,U=U2,X = X,V = V, Z = Z, W = W,eta=eta2)
  if(n1>0){
    IC=rep(1,n);X2=cbind(X2,IC)
    ind=sample(which(X2$U==1&X2$y==1),min(n1,sum(X2$U==1&X2$y==1)))
    X2$L[ind]=X2$T[ind];X2$R[ind]=X2$T[ind];
    X2$y[ind]=3;X2$IC[ind]=0}
  X2 <- X2 %>% arrange(IC)
  if(n1==0){
    X2 = X2
  }
  X2 = cbind(X2,IC)
  
  cr.t <- c(sum(X1$R==Inf)/n,sum(X2$R==Inf)/n)
  cr.cure<- c(sum(X1$U==0)/n,sum(X2$U==0)/n)
  
  return(list(X1 = X1, X2 = X2, cr.t = cr.t, cr.cure = cr.cure))
}
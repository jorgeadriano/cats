package cats
package laws

import cats.kernel.CommutativeMonoid

trait UnorderedFoldableLaws[F[_]] {
  implicit def F: UnorderedFoldable[F]

  def unorderedFoldConsistentWithUnorderedFoldMap[A: CommutativeMonoid](fa: F[A]): IsEq[A] =
    F.unorderedFoldMap(fa)(identity) <-> F.unorderedFold(fa)

  def unorderedReduceOptionConsistentWithUnorderedFold[A: CommutativeMonoid](fa: F[A]): IsEq[Option[A]] =
    F.unorderedReduceOption(fa) <-> (if (F.isEmpty(fa)) None else Some(F.unorderedFold(fa)))

  def forallConsistentWithExists[A](fa: F[A], p: A => Boolean): Boolean =
    if (F.forall(fa)(p)) {
      val negationExists = F.exists(fa)(a => !(p(a)))

      // if p is true for all elements, then there cannot be an element for which
      // it does not hold.
      !negationExists &&
      // if p is true for all elements, then either there must be no elements
      // or there must exist an element for which it is true.
      (F.isEmpty(fa) || F.exists(fa)(p))
    } else true // can't test much in this case

  def existsLazy[A](fa: F[A]): Boolean = {
    var i = 0
    F.exists(fa) { _ =>
      i += 1
      true
    }
    i == (if (F.isEmpty(fa)) 0 else 1)
  }

  def forallLazy[A](fa: F[A]): Boolean = {
    var i = 0
    F.forall(fa) { _ =>
      i += 1
      false
    }
    i == (if (F.isEmpty(fa)) 0 else 1)
  }

  /**
   * If `F[A]` is empty, forall must return true.
   */
  def forallEmpty[A](fa: F[A], p: A => Boolean): Boolean =
    !F.isEmpty(fa) || F.forall(fa)(p)

  def nonEmptyRef[A](fa: F[A]): IsEq[Boolean] =
    F.nonEmpty(fa) <-> !F.isEmpty(fa)

  /**
   * If there are elements in `F[A]` there exists a minimum
   */
  def minimumOptionIsMinimal[A](fa: F[A])(implicit A: Order[A]): Boolean = {
    val optMin = F.minimumOption(fa)
    F.forall(fa) { a =>
      optMin.exists { min =>
        A.lteqv(min, a)
      }
    }
  }

  /**
   * If `F[A]` has a minimum this minimum is contained in `F[A]`
   */
  def minimumOptionIsContained[A: Order](fa: F[A]): Boolean =
    F.minimumOption(fa).forall { min =>
      F.exists(fa) { a =>
        Order.eqv(min, a)
      }
    }

  /**
   * If there are elements in `F[A]` there exists a maximum
   */
  def maximumOptionIsMaximal[A](fa: F[A])(implicit A: Order[A]): Boolean = {
    val optMax = F.maximumOption(fa)
    F.forall(fa) { a =>
      optMax.exists { max =>
        A.gteqv(max, a)
      }
    }
  }

  /**
   * If `F[A]` has a maximum this maximum is contained in `F[A]`
   */
  def maximumOptionIsContained[A: Order](fa: F[A]): Boolean =
    F.maximumOption(fa).forall { max =>
      F.exists(fa) { a =>
        Order.eqv(max, a)
      }
    }

  /**
   * If there are elements in `F[A]` there exists a minimum by measure f
   */
  def minimumByOptionIsMinimal[A, B](fa: F[A], f: A => B)(implicit B: Order[B]): Boolean = {
    val optMin = F.minimumByOption(fa)(f).map(f)
    F.forall(fa) { a =>
      optMin.exists { min =>
        B.lteqv(min, f(a))
      }
    }
  }

  /**
   * If `F[A]` has a minimum by some measure f this minimum is contained in `F[A]`
   */
  def minimumByOptionIsContained[A, B: Order](fa: F[A], f: A => B)(implicit A: Equiv[A]): Boolean =
    F.minimumByOption(fa)(f).forall { min =>
      F.exists(fa) { a =>
        A.equiv(min, a)
      }
    }

  /**
   * If there are elements in `F[A]` there exists a maximum by measure f
   */
  def maximumByOptionIsMaximal[A, B](fa: F[A], f: A => B)(implicit B: Order[B]): Boolean = {
    val optMax = F.maximumByOption(fa)(f).map(f)
    F.forall(fa) { a =>
      optMax.exists { max =>
        B.gteqv(max, f(a))
      }
    }
  }

  /**
   * If `F[A]` has a maximum by some measure f this maximum is contained in `F[A]`
   */
  def maximumByOptionIsContained[A, B: Order](fa: F[A], f: A => B)(implicit A: Equiv[A]): Boolean =
    F.maximumByOption(fa)(f).forall { max =>
      F.exists(fa) { a =>
        A.equiv(max, a)
      }
    }

}

object UnorderedFoldableLaws {
  def apply[F[_]](implicit ev: UnorderedFoldable[F]): UnorderedFoldableLaws[F] =
    new UnorderedFoldableLaws[F] { def F: UnorderedFoldable[F] = ev }
}

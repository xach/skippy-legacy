;;; 
;;; skippy.asd
;;; 
;;; Created: 2005-03-06 by Zach Beane <xach@xach.com>
;;; 
;;; This file is released into the public domain.
;;; 
;;; $Id: skippy.asd,v 1.1.1.1 2005/03/06 15:36:00 xach Exp $

(defpackage :skippy-system
  (:use :cl :asdf))

(in-package :skippy-system)

(defsystem :skippy-legacy
  :components ((:file "skippy")))

